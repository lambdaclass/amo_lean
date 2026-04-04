"""Split generated C/Rust programs and build validation wrappers.

The generated programs have structure:
  [includes + NTT function(s)] ... int main(void) { ... }  (C)
  [uses + NTT function(s)] ... fn main() { ... }           (Rust)

We split at main() to extract the NTT kernel, then wrap it in a
validation main that prints all output elements for Python comparison.
"""

import re
from field_defs import FieldDef
from lean_driver import GeneratedProgram


def split_at_main(source: str, lang: str) -> tuple[str, str]:
    """Split source into (kernel, main_section).

    For C: split at 'int main(void)' or 'int main()'
    For Rust: split at 'fn main()'
    """
    if lang == "c":
        pattern = r'\nint main\s*\(void\)\s*\{'
    else:
        pattern = r'\nfn main\s*\(\)\s*\{'

    match = re.search(pattern, source)
    if not match:
        raise ValueError(f"Could not find main() in {lang} source")
    kernel = source[:match.start()]
    main_section = source[match.start():]
    return kernel, main_section


def _detect_ntt_func_name(kernel: str, lang: str) -> str:
    """Find the NTT function name in the kernel."""
    if lang == "c":
        # Look for: void XXX_ntt_ultra(int32_t* data, ...)
        m = re.search(r'void\s+(\w+_ntt_ultra)\s*\(', kernel)
        if m:
            return m.group(1)
        # Fallback: look for any void XXX(int32_t* data, const int32_t* twiddles)
        m = re.search(r'void\s+(\w+)\s*\(\s*(?:int32_t|int64_t)\s*\*\s*data', kernel)
        if m:
            return m.group(1)
    else:
        m = re.search(r'fn\s+(\w+_ntt_ultra\w*)\s*\(', kernel)
        if m:
            return m.group(1)
        m = re.search(r'fn\s+(\w+)\s*\(\s*data\s*:', kernel)
        if m:
            return m.group(1)
    raise ValueError(f"Could not detect NTT function name in {lang} kernel")


def build_validation_c(kernel: str, field: FieldDef, log_n: int, func_name: str) -> str:
    """Build a C validation program that prints all NTT output elements."""
    n = 1 << log_n
    tw_sz = n * log_n
    p = field.p
    R = field.R
    elem = field.elem_c
    wide = field.wide_c

    # For Goldilocks, use unsigned types for init
    if field.k == 64:
        init_cast = "(uint64_t)"
        r_lit = f"((__uint128_t)1 << 64)"
        p_lit = f"{p}ULL"
        print_fmt = '    printf("%llu\\n", (unsigned long long)(((unsigned __int128)d[i]) % ((unsigned __int128){p_lit})));'
    else:
        init_cast = f"({wide})"
        r_lit = "4294967296ULL"
        p_lit = f"{p}U"
        print_fmt = f'    printf("%lld\\n", (long long)(({wide})d[i] % ({wide}){p_lit}));'

    g = field.generator

    return f"""{kernel}

#include <stdio.h>
#include <stdlib.h>

static {wide} val_mod_pow({wide} base, {wide} exp, {wide} m) {{
    {wide} result = 1;
    base %= m;
    while (exp > 0) {{
        if (exp & 1) result = ({wide})(((unsigned __int128)result * base) % m);
        base = ({wide})(((unsigned __int128)base * base) % m);
        exp >>= 1;
    }}
    return result;
}}

int main(void) {{
    size_t n = {n};
    size_t logn = {log_n};
    size_t tw_sz = {tw_sz};
    {wide} p_val = ({wide}){p_lit};
    {elem} *d = ({elem}*)malloc(n * sizeof({elem}));
    {elem} *tw = ({elem}*)malloc(tw_sz * sizeof({elem}));
    {elem} *tw_mont = ({elem}*)malloc(tw_sz * sizeof({elem}));
    /* Data init */
    for (size_t i = 0; i < n; i++)
        d[i] = ({elem})((({wide})i * 1000000007) % {init_cast}{p_lit});
    /* Real roots of unity: omega_n = g^((p-1)/n) mod p */
    {wide} omega_n = val_mod_pow({g}, (p_val - 1) / n, p_val);
    for (size_t st = 0; st < logn; st++) {{
        size_t h = 1u << (logn - 1 - st);
        for (size_t gg = 0; gg < (1u << st); gg++)
            for (size_t pp = 0; pp < h; pp++)
                tw[st*(n/2) + gg*h + pp] = ({elem})val_mod_pow(omega_n, pp*(1ULL<<st), p_val);
    }}
    /* Montgomery twiddles for AMO ultra: tw_mont = tw * R mod p */
    for (size_t i = 0; i < tw_sz; i++)
        tw_mont[i] = ({elem})((({wide})tw[i] * {r_lit}) % {init_cast}{p_lit});
    /* Run NTT */
    {func_name}(d, tw_mont);
    /* Print output mod p */
    for (size_t i = 0; i < n; i++)
{print_fmt}
    free(d);
    free(tw_mont);
    return 0;
}}
"""


def build_validation_rust(kernel: str, field: FieldDef, log_n: int, func_name: str) -> str:
    """Build a Rust validation program that prints all NTT output elements."""
    n = 1 << log_n
    tw_sz = n * log_n
    p = field.p

    if field.k == 64:
        et = "u64"
        wt = "u128"
        r_val = "1u128 << 64"
    else:
        et = "u32"
        wt = "i64"
        r_val = "4294967296i64"

    return f"""{kernel}

fn main() {{
    let n: usize = {n};
    let tw_sz: usize = {tw_sz};
    let p: {wt} = {p};
    let mut d: Vec<{et}> = (0..n).map(|i| ((i as {wt} * 1000000007) % p) as {et}).collect();
    let tw_mont: Vec<{et}> = (0..tw_sz).map(|i| {{
        let base = ((i as {wt}) * 7 + 31) % p;
        ((base * {r_val}) % p) as {et}
    }}).collect();
    unsafe {{
        let data_ptr = d.as_mut_ptr() as *mut i32;
        let data_slice = std::slice::from_raw_parts_mut(data_ptr, n);
        let tw_ptr = tw_mont.as_ptr() as *const i32;
        let tw_slice = std::slice::from_raw_parts(tw_ptr, tw_sz);
        {func_name}(data_slice, tw_slice);
    }}
    for i in 0..n {{
        let v = (d[i] as {wt}).rem_euclid(p);
        println!("{{}}", v);
    }}
}}
"""


def generate_validation_program(program: GeneratedProgram, field: FieldDef) -> str:
    """Extract NTT kernel from generated program and build validation wrapper."""
    kernel, _ = split_at_main(program.source, program.lang)
    func_name = _detect_ntt_func_name(kernel, program.lang)

    if program.lang == "c":
        return build_validation_c(kernel, field, program.log_n, func_name)
    else:
        return build_validation_rust(kernel, field, program.log_n, func_name)
