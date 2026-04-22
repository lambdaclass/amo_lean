"""Field definitions for AMO-Lean NTT benchmark harness.

Constants match OptimizedNTTPipeline.lean:89-120 and Bench.lean:60-88.
"""

from dataclasses import dataclass


@dataclass(frozen=True)
class FieldDef:
    name: str           # "babybear", "koalabear", "mersenne31", "goldilocks"
    display: str        # "BabyBear", etc.
    p: int              # prime
    c: int              # Solinas correction constant
    k: int              # shift bits (31 or 64)
    generator: int      # primitive root for NTT
    mu: int             # Montgomery inverse: p^{-1} mod R
    R: int              # Montgomery constant: 2^32 or 2^64
    elem_c: str         # C element type
    wide_c: str         # C wide type
    elem_rs: str        # Rust element type (unsigned)
    wide_rs: str        # Rust wide type


BABYBEAR = FieldDef(
    name="babybear", display="BabyBear",
    p=2013265921, c=134217727, k=31, generator=31,
    mu=0x88000001, R=2**32,
    elem_c="int32_t", wide_c="int64_t",
    elem_rs="u32", wide_rs="i64",
)

KOALABEAR = FieldDef(
    name="koalabear", display="KoalaBear",
    p=2130706433, c=16777215, k=31, generator=3,
    mu=0x81000001, R=2**32,
    elem_c="int32_t", wide_c="int64_t",
    elem_rs="u32", wide_rs="i64",
)

MERSENNE31 = FieldDef(
    name="mersenne31", display="Mersenne31",
    p=2147483647, c=1, k=31, generator=7,
    mu=0x7FFFFFFF, R=2**32,
    elem_c="int32_t", wide_c="int64_t",
    elem_rs="u32", wide_rs="i64",
)

GOLDILOCKS = FieldDef(
    name="goldilocks", display="Goldilocks",
    p=18446744069414584321, c=4294967295, k=64, generator=7,
    mu=0, R=2**64,
    elem_c="uint64_t", wide_c="__uint128_t",
    elem_rs="u64", wide_rs="u128",
)

ALL_FIELDS = {f.name: f for f in [BABYBEAR, KOALABEAR, MERSENNE31, GOLDILOCKS]}

def get_field(name: str) -> FieldDef:
    if name not in ALL_FIELDS:
        raise ValueError(f"Unknown field: {name}. Choose from: {list(ALL_FIELDS.keys())}")
    return ALL_FIELDS[name]
