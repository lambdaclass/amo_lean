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


def _ntt_call(kernel: str, func_name: str, data: str = "d",
              tw: str = "tw_mont", mu_tw: str = "mu_tw") -> str:
    """Generate the NTT function call with correct number of arguments.
    Detects 3-arg (sqdmulh: data, twiddles, mu_tw) vs 2-arg (vmull: data, twiddles)
    by checking the function signature in the kernel."""
    # Look for the function signature to count parameters
    import re
    sig_match = re.search(rf'void\s+{re.escape(func_name)}\s*\(([^)]*)\)', kernel)
    if sig_match:
        params = sig_match.group(1).split(',')
        if len(params) >= 3:
            return f"{func_name}({data}, {tw}, {mu_tw})"
    return f"{func_name}({data}, {tw})"


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
    /* Precomputed mu_tw for sqdmulh REDC: mu_tw[i] = tw_mont[i] * mu mod 2^32 */
    {elem} *mu_tw = ({elem}*)malloc(tw_sz * sizeof({elem}));
    for (size_t i = 0; i < tw_sz; i++)
        mu_tw[i] = ({elem})((({wide})tw_mont[i] * ({wide}){field.mu}U) & 0xFFFFFFFFULL);
    /* Run NTT */
    {_ntt_call(kernel, func_name)};
    /* Print output mod p */
    for (size_t i = 0; i < n; i++)
{print_fmt}
    free(d);
    free(tw_mont);
    free(mu_tw);
    return 0;
}}
"""


def _detect_is_neon(kernel: str) -> bool:
    """Check if the kernel uses NEON intrinsics."""
    return "arm_neon.h" in kernel or "vld1q_s32" in kernel


def _inject_neon_debug(kernel: str, p: int, k: int, c: int, mu: int) -> str:
    """Inject a debug butterfly that prints lane-0 intermediates for the first call.

    Creates neon_bf_dit_debug (copy of neon_bf_dit with printf after each step),
    and patches the FIRST butterfly call in stage 0 to use it.
    """
    # Find the neon_bf_dit function body
    bf_match = re.search(
        r'(static inline void neon_bf_dit\([^)]*\)\s*\{)(.*?)(\})\s*\n',
        kernel, re.DOTALL
    )
    if not bf_match:
        return kernel  # Can't find butterfly, skip debug

    bf_sig = bf_match.group(1)
    bf_body = bf_match.group(2)

    # Build debug version: insert printf after key assignments
    debug_prints = f"""
  /* DEBUG: print lane 0 intermediates */
  printf("NEON_BF lane0: a=%d b=%d tw=%d\\n",
    vgetq_lane_s32(a,0), vgetq_lane_s32(b,0), vgetq_lane_s32(tw,0));
  printf("NEON_BF lane0: prod_lo=%llu prod_hi=%llu\\n",
    (unsigned long long)vgetq_lane_u64(prod_lo,0),
    (unsigned long long)vgetq_lane_u64(prod_hi,0));
  printf("NEON_BF lane0: tl=%u m=%u\\n",
    vget_lane_u32(tl_lo,0), vget_lane_u32(m_lo,0));
  printf("NEON_BF lane0: u_lo=%llu\\n",
    (unsigned long long)vgetq_lane_u64(u_lo,0));
  printf("NEON_BF lane0: d_lo=%lld q=%d\\n",
    (long long)vgetq_lane_s64(d_lo,0), vgetq_lane_s32(q,0));
  printf("NEON_BF lane0: fixup=%u wb_red=%d\\n",
    vgetq_lane_u32(fixup,0), vgetq_lane_s32(wb_red,0));
  printf("NEON_BF lane0: sum_raw=%u diff_raw=%u\\n",
    vgetq_lane_u32(sum_raw,0), vgetq_lane_u32(diff_raw,0));
  printf("NEON_BF lane0: sum_fold=%u diff_fold=%u\\n",
    vgetq_lane_u32(sum_fold,0), vgetq_lane_u32(diff_fold,0));
"""
    # Insert debug prints before the stores (vst1q_s32 lines)
    store_pattern = r'(\s*vst1q_s32\(a_ptr)'
    debug_body = re.sub(store_pattern, debug_prints + r'\1', bf_body, count=1)

    # Create debug function (renamed)
    debug_func = (
        bf_sig.replace("neon_bf_dit", "neon_bf_dit_debug")
        + debug_body + "}\n\n"
    )

    # Insert debug function right after the original
    insertion_point = bf_match.end()
    kernel_with_debug = kernel[:insertion_point] + debug_func + kernel[insertion_point:]

    # Patch the FIRST butterfly call in the first stage to use debug version
    # Pattern: neon_bf_dit(&data[... (first occurrence in a stage comment block)
    kernel_with_debug = kernel_with_debug.replace(
        "neon_bf_dit(&data[", "neon_bf_dit_debug(&data[", 1
    )

    return kernel_with_debug


def _inject_scalar_debug(kernel: str) -> str:
    """Inject printf in the first butterfly of the scalar verified kernel.

    The scalar kernel uses variables like a_val, b_val, w_val, t0..tN.
    We inject a printf after the first butterfly block (identified by the first
    'data[j] = ...' store pattern in stage 0).
    """
    # Find the first stage block and inject printf after the first butterfly
    # Scalar verified code has pattern: data[i] = tN; data[j] = tM;
    # We inject a printf after the first pair of stores
    stage0_pattern = r'(/\* Stage 0:.*?\*/)'
    m = re.search(stage0_pattern, kernel)
    if not m:
        return kernel

    # Find the first "data[" store after stage 0 comment
    # The butterfly stores a_val and b_val — after the butterfly computation
    # We inject printf to print the key variables after the FIRST iteration
    # of the inner loop (pair == 0)
    #
    # Strategy: inject a debug block at the very start of the stage 0 loop body
    # that fires only once (using a static flag)
    debug_block = """
    { /* DEBUG: scalar butterfly intermediates (first call only) */
      static int _dbg_done = 0;
      if (!_dbg_done) {
        _dbg_done = 1;
        printf("SCALAR_BF: a=%lld b=%lld tw=%lld\\n",
          (long long)a_val, (long long)b_val, (long long)w_val);
        /* t0=product, t1=m, t2=u, t3=d, t4=q, t5=wb_red via ite */
        printf("SCALAR_BF: t0=%lld t1=%lld t2=%lld t3=%lld t4=%lld\\n",
          (long long)t0, (long long)t1, (long long)t2,
          (long long)t3, (long long)t4);
      }
    }
"""
    # Find the first store-pair pattern after stage 0:
    # data[...] = tN;  (store sum)
    # data[...] = tM;  (store diff)
    stores = list(re.finditer(r'data\[\w+\]\s*=\s*(t\d+);', kernel[m.start():]))
    if len(stores) >= 2:
        # Insert debug after the second store (end of first butterfly)
        insert_pos = m.start() + stores[1].end()
        kernel = kernel[:insert_pos] + "\n" + debug_block + kernel[insert_pos:]

    return kernel


def build_debug_validation_c(kernel: str, field: FieldDef, log_n: int,
                              func_name: str) -> str:
    """Build a C validation program with debug printf instrumentation.

    Injects printf to print:
    - Twiddles and data before NTT (ND.4)
    - Butterfly intermediates for first call (ND.2/ND.3)
    Detects NEON vs scalar automatically.
    """
    is_neon = _detect_is_neon(kernel)

    if is_neon:
        kernel = _inject_neon_debug(kernel, field.p, field.k, field.c, field.mu)
    else:
        kernel = _inject_scalar_debug(kernel)

    n = 1 << log_n
    tw_sz = n * log_n
    p = field.p
    R = field.R
    elem = field.elem_c
    wide = field.wide_c

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

    # ND.4: Twiddle and data dump before NTT
    pre_ntt_debug = f"""
    /* === DEBUG: ND.4 twiddle + data dump === */
    printf("=== TWIDDLE DUMP (first 8) ===\\n");
    for (size_t _i = 0; _i < 8 && _i < tw_sz; _i++)
        printf("tw_mont[%zu]=%lld (plain tw[%zu]=%lld)\\n",
               _i, (long long)tw_mont[_i], _i, (long long)tw[_i]);
    printf("=== DATA DUMP (first 16) ===\\n");
    for (size_t _i = 0; _i < 16 && _i < n; _i++)
        printf("data[%zu]=%lld\\n", _i, (long long)d[_i]);
    printf("=== RUNNING {'NEON' if is_neon else 'SCALAR'} NTT ===\\n");
"""

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
{pre_ntt_debug}
    /* Precomputed mu_tw for sqdmulh REDC */
    {elem} *mu_tw = ({elem}*)malloc(tw_sz * sizeof({elem}));
    for (size_t i = 0; i < tw_sz; i++)
        mu_tw[i] = ({elem})((({wide})tw_mont[i] * ({wide}){field.mu}U) & 0xFFFFFFFFULL);
    /* Run NTT */
    {_ntt_call(kernel, func_name)};
    /* Print output mod p */
    for (size_t i = 0; i < n; i++)
{print_fmt}
    free(d);
    free(tw);
    free(tw_mont);
    return 0;
}}
"""


def build_validation_rust(kernel: str, field: FieldDef, log_n: int, func_name: str,
                          rust_simd: bool = False) -> str:
    """Build a Rust validation program that prints all NTT output elements.
    Uses real roots of unity in Montgomery form matching the benchmark harness."""
    n = 1 << log_n
    tw_sz = n * log_n
    p = field.p
    g = field.generator

    if field.k == 64:
        et = "u64"
        wt = "u128"
        r_val = f"1{wt} << 64"
    else:
        et = "u32"
        wt = "u64"
        r_val = f"4294967296_{wt}"

    return f"""{kernel}

fn main() {{
    let n: usize = {n};
    let logn: usize = {log_n};
    let tw_sz: usize = {tw_sz};
    let p: {wt} = {p};
    let mut d: Vec<{et}> = (0..n).map(|i| ((i as {wt} * 1000000007) % p) as {et}).collect();
    /* Real roots of unity: omega_n = g^((p-1)/n) mod p */
    let omega_n = mod_pow({g}, (p - 1) / n as {wt}, p);
    let mut tw: Vec<{et}> = vec![0; tw_sz];
    for st in 0..logn {{
        let h = 1usize << (logn - 1 - st);
        for grp in 0..(1usize << st) {{
            for pp in 0..h {{
                tw[st * (n/2) + grp * h + pp] = mod_pow(omega_n, (pp as {wt}) * (1_{wt} << st), p) as {et};
            }}
        }}
    }}
    /* Montgomery twiddles: tw_mont = tw * R mod p */
    let tw_mont: Vec<{et}> = tw.iter().map(|&t| ((t as {wt} * {r_val}) % p) as {et}).collect();
    {"let mu: " + wt + " = " + str(field.mu) + "; let mu_tw: Vec<" + et + "> = tw_mont.iter().map(|&t| ((t as " + wt + " * mu) & 0xFFFFFFFF) as " + et + ").collect(); unsafe { " + func_name + "(d.as_mut_ptr() as *mut i32, tw_mont.as_ptr() as *const i32, mu_tw.as_ptr() as *const i32) }" if rust_simd else func_name + "(&mut d, &tw_mont)"};
    for i in 0..n {{
        let v = (d[i] as {wt}).rem_euclid(p);
        println!("{{}}", v);
    }}
}}
"""


def generate_validation_program(program: GeneratedProgram, field: FieldDef,
                                debug: bool = False, rust_simd: bool = False) -> str:
    """Extract NTT kernel from generated program and build validation wrapper.

    If debug=True, injects printf instrumentation for NEON butterfly debugging.
    """
    kernel, _ = split_at_main(program.source, program.lang)
    func_name = _detect_ntt_func_name(kernel, program.lang)

    if program.lang == "c":
        if debug:
            return build_debug_validation_c(kernel, field, program.log_n, func_name)
        return build_validation_c(kernel, field, program.log_n, func_name)
    else:
        return build_validation_rust(kernel, field, program.log_n, func_name, rust_simd=rust_simd)
