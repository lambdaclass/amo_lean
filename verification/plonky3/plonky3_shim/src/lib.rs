//! Plonky3 C FFI Shim
//!
//! This crate provides C-compatible wrappers for Plonky3's NTT operations
//! on the Goldilocks field.
//!
//! # Safety
//!
//! All functions use `catch_unwind` to prevent Rust panics from crossing
//! the FFI boundary. Error codes are returned instead.
//!
//! # Usage from C
//!
//! ```c
//! void* lib = dlopen("./libplonky3_shim.so", RTLD_NOW);
//! int (*ntt)(uint64_t*, size_t) = dlsym(lib, "plonky3_ntt_forward");
//! ntt(data, len);
//! ```

use std::panic::catch_unwind;
use std::slice;

use p3_dft::{Radix2Dit, TwoAdicSubgroupDft};
use p3_field::{Field, PrimeField32, PrimeField64, TwoAdicField};
use p3_goldilocks::Goldilocks;
use p3_baby_bear::BabyBear;
use p3_koala_bear::KoalaBear;
use p3_matrix::dense::RowMajorMatrix;

/// Goldilocks prime: p = 2^64 - 2^32 + 1
const GOLDILOCKS_PRIME: u64 = 0xFFFF_FFFF_0000_0001;

/// BabyBear prime: p = 2^31 - 2^27 + 1 = 2013265921
const BABYBEAR_PRIME: u32 = 2013265921;

// ============================================================================
// NTT Functions
// ============================================================================

/// Compute forward NTT (DFT) in place using Plonky3's Radix-2 DIT algorithm.
///
/// # Arguments
/// * `data` - Pointer to array of `len` u64 values (field elements)
/// * `len` - Number of elements (must be power of 2)
///
/// # Returns
/// * 0 on success
/// * -1 on error (null pointer, invalid length, or panic)
///
/// # Safety
/// * `data` must point to a valid array of at least `len` u64 values
/// * `len` must be a power of 2
#[no_mangle]
pub unsafe extern "C" fn plonky3_ntt_forward(data: *mut u64, len: usize) -> i32 {
    // Validate inputs
    if data.is_null() {
        return -1;
    }
    if len == 0 || (len & (len - 1)) != 0 {
        return -1; // len must be power of 2
    }

    // Wrap in catch_unwind to prevent panics crossing FFI
    let result = catch_unwind(|| {
        let slice = slice::from_raw_parts_mut(data, len);

        // Convert u64 -> Goldilocks
        // Note: Goldilocks::new() accepts any u64, reduction happens lazily
        let values: Vec<Goldilocks> = slice.iter().map(|&x| Goldilocks::new(x)).collect();

        // Create a matrix with width=1 (single column of values)
        let mat = RowMajorMatrix::new(values, 1);

        // Apply NTT using Radix-2 DIT
        let dft = Radix2Dit::default();
        let result = dft.dft_batch(mat);

        // Copy results back to the input array
        for (i, v) in result.values.iter().enumerate() {
            slice[i] = v.as_canonical_u64();
        }
    });

    match result {
        Ok(_) => 0,
        Err(_) => -1,
    }
}

/// Compute inverse NTT (IDFT) in place.
///
/// # Arguments
/// * `data` - Pointer to array of `len` u64 values (field elements)
/// * `len` - Number of elements (must be power of 2)
///
/// # Returns
/// * 0 on success
/// * -1 on error
///
/// # Safety
/// Same requirements as `plonky3_ntt_forward`
#[no_mangle]
pub unsafe extern "C" fn plonky3_ntt_inverse(data: *mut u64, len: usize) -> i32 {
    if data.is_null() {
        return -1;
    }
    if len == 0 || (len & (len - 1)) != 0 {
        return -1;
    }

    let result = catch_unwind(|| {
        let slice = slice::from_raw_parts_mut(data, len);

        let values: Vec<Goldilocks> = slice.iter().map(|&x| Goldilocks::new(x)).collect();
        let mat = RowMajorMatrix::new(values, 1);

        let dft = Radix2Dit::default();
        let result = dft.idft_batch(mat);

        for (i, v) in result.values.iter().enumerate() {
            slice[i] = v.as_canonical_u64();
        }
    });

    match result {
        Ok(_) => 0,
        Err(_) => -1,
    }
}

// ============================================================================
// Scalar-only NTT (v3.10.1 AC-2: fair baseline comparison)
// ============================================================================

/// Compute forward NTT using SCALAR Goldilocks field ops only.
/// No PackedGoldilocksNeon, no inline asm, no 2-lane parallelism.
/// Uses Goldilocks::mul/add/sub directly in a standard DIT butterfly.
/// This measures: Rust-compiled scalar vs our C-generated scalar (same algorithm).
///
/// # Safety
/// Same requirements as `plonky3_ntt_forward`
#[no_mangle]
pub unsafe extern "C" fn plonky3_ntt_forward_scalar(data: *mut u64, len: usize) -> i32 {
    if data.is_null() { return -1; }
    if len == 0 || (len & (len - 1)) != 0 { return -1; }

    let result = catch_unwind(|| {
        let slice = slice::from_raw_parts_mut(data, len);
        let log_n = len.trailing_zeros() as usize;

        // Convert to Goldilocks
        let mut d: Vec<Goldilocks> = slice.iter().map(|&x| Goldilocks::new(x)).collect();

        // Precompute twiddles (same CT standard convention as our reference_ntt.py)
        let omega_n = Goldilocks::two_adic_generator(log_n);
        let tw_sz = len * log_n;
        let mut tw: Vec<Goldilocks> = vec![Goldilocks::new(0); tw_sz];
        for stage in 0..log_n {
            let half = len >> (stage + 1);
            // omega_stage = omega_n^(2^stage) via repeated squaring
            let mut omega_stage = omega_n;
            for _ in 0..stage { omega_stage = omega_stage * omega_stage; }
            // tw[stage*(len/2) + pair] = omega_stage^pair
            let mut w = Goldilocks::new(1);
            for pair in 0..half {
                tw[stage * (len / 2) + pair] = w;
                w = w * omega_stage;
            }
        }

        // DIT NTT with scalar field ops (same structure as our lowerStageVerified)
        for stage in 0..log_n {
            let half = len >> (stage + 1);
            let num_groups = 1usize << stage;
            for group in 0..num_groups {
                for pair in 0..half {
                    let i = group * 2 * half + pair;
                    let j = i + half;
                    let w = tw[stage * (len / 2) + pair];
                    // Butterfly: sum = a + w*b, diff = a - w*b
                    let a = d[i];
                    let b = d[j];
                    let wb = w * b;
                    d[i] = a + wb;
                    d[j] = a - wb;
                }
            }
        }

        // Copy back
        for (i, v) in d.iter().enumerate() {
            slice[i] = v.as_canonical_u64();
        }
    });

    match result {
        Ok(_) => 0,
        Err(_) => -1,
    }
}

// ============================================================================
// Field Information Functions
// ============================================================================

/// Get the Goldilocks prime modulus.
///
/// # Returns
/// The prime p = 2^64 - 2^32 + 1
#[no_mangle]
pub extern "C" fn plonky3_goldilocks_prime() -> u64 {
    GOLDILOCKS_PRIME
}

/// Get the two-adic generator for a given size.
///
/// # Arguments
/// * `log_n` - log2 of the NTT size (e.g., 8 for N=256)
///
/// # Returns
/// * The primitive N-th root of unity (omega)
/// * 0 if log_n > 32 (Goldilocks has 2-adicity of 32)
#[no_mangle]
pub extern "C" fn plonky3_get_omega(log_n: usize) -> u64 {
    if log_n > 32 {
        return 0;
    }
    Goldilocks::two_adic_generator(log_n).as_canonical_u64()
}

/// Check if Plonky3 uses Montgomery representation internally.
///
/// # Returns
/// * 0 if standard representation (value stored directly)
/// * 1 if Montgomery representation (value stored as a*R mod p)
///
/// This is useful for debugging compatibility issues.
#[no_mangle]
pub extern "C" fn plonky3_is_montgomery() -> i32 {
    // Create field element 1 and check its internal representation
    let one = Goldilocks::new(1);
    let canonical = one.as_canonical_u64();

    // If canonical value equals 1, it's standard representation
    // If canonical value equals R^-1 mod p, it's Montgomery
    if canonical == 1 {
        0 // Standard
    } else {
        1 // Montgomery
    }
}

// ============================================================================
// BabyBear NTT Functions (31-bit prime, MontyField31 internally)
// ============================================================================

/// Compute forward NTT on BabyBear field elements in place.
///
/// Uses Plonky3's Radix2Dit with MontyField31<BabyBearParameters>.
/// This is the REAL Plonky3 NTT — not a simplified reference.
/// On ARM, Plonky3 uses NEON intrinsics (sqdmulh Montgomery) automatically.
///
/// # Arguments
/// * `data` - Pointer to array of `len` u32 values (field elements in [0, p))
/// * `len` - Number of elements (must be power of 2)
///
/// # Returns
/// * 0 on success, -1 on error
///
/// # Safety
/// * `data` must point to a valid array of at least `len` u32 values
#[no_mangle]
pub unsafe extern "C" fn plonky3_babybear_ntt_forward(data: *mut u32, len: usize) -> i32 {
    if data.is_null() || len == 0 || (len & (len - 1)) != 0 {
        return -1;
    }

    let result = catch_unwind(|| {
        let slice = slice::from_raw_parts_mut(data, len);
        let values: Vec<BabyBear> = slice
            .iter()
            .map(|&x| BabyBear::new(x))
            .collect();
        let mat = RowMajorMatrix::new(values, 1);
        let dft: Radix2Dit<BabyBear> = Radix2Dit::default();
        let result = dft.dft_batch(mat);
        for (i, v) in result.values.iter().enumerate() {
            slice[i] = PrimeField32::as_canonical_u32(v);
        }
    });

    match result {
        Ok(_) => 0,
        Err(_) => -1,
    }
}

/// Get the BabyBear prime modulus.
#[no_mangle]
pub extern "C" fn plonky3_babybear_prime() -> u32 {
    BABYBEAR_PRIME
}

// ============================================================================
// KoalaBear NTT Functions (31-bit prime, MontyField31 internally)
// ============================================================================

/// KoalaBear prime: p = 2^31 - 2^24 + 1 = 2130706433
const KOALABEAR_PRIME: u32 = 2130706433;

/// Compute forward NTT on KoalaBear field elements in place.
///
/// Uses Plonky3's Radix2Dit with MontyField31<KoalaBearParameters>.
/// On ARM, Plonky3 uses NEON intrinsics automatically.
///
/// # Safety
/// * `data` must point to a valid array of at least `len` u32 values
#[no_mangle]
pub unsafe extern "C" fn plonky3_koalabear_ntt_forward(data: *mut u32, len: usize) -> i32 {
    if data.is_null() || len == 0 || (len & (len - 1)) != 0 {
        return -1;
    }

    let result = catch_unwind(|| {
        let slice = slice::from_raw_parts_mut(data, len);
        let values: Vec<KoalaBear> = slice
            .iter()
            .map(|&x| KoalaBear::new(x))
            .collect();
        let mat = RowMajorMatrix::new(values, 1);
        let dft: Radix2Dit<KoalaBear> = Radix2Dit::default();
        let result = dft.dft_batch(mat);
        for (i, v) in result.values.iter().enumerate() {
            slice[i] = PrimeField32::as_canonical_u32(v);
        }
    });

    match result {
        Ok(_) => 0,
        Err(_) => -1,
    }
}

/// Get the KoalaBear prime modulus.
#[no_mangle]
pub extern "C" fn plonky3_koalabear_prime() -> u32 {
    KOALABEAR_PRIME
}

/// Get the two-adic generator for BabyBear at a given size.
/// BabyBear has 2-adicity of 27.
#[no_mangle]
pub extern "C" fn plonky3_babybear_get_omega(log_n: usize) -> u32 {
    if log_n > 27 {
        return 0;
    }
    BabyBear::two_adic_generator(log_n).as_canonical_u32()
}

// ============================================================================
// NOTE: Mersenne31 NTT is NOT available via Radix2Dit.
// Mersenne31 (p = 2^31 - 1) is NOT two-adic (2-adicity = 1).
// Plonky3 uses Complex<Mersenne31> (quadratic extension) for NTT.
// Direct comparison with our base-field Mersenne31 NTT is not applicable.
// ============================================================================

// ============================================================================
// Batch NTT Functions (v3.19 N319.2.1)
//
// Expose `dft_batch` with parametric `width` to measure Plonky3 batch
// optimizations (PackedMontyField31Neon for BabyBear/KoalaBear, Radix2DitParallel,
// etc.) that are bypassed by the single-vector functions above (which hardcode
// width=1). See research/TRZK_SBB.md §13.2 for the width=1 caveat and §13.3 for
// the batch measurement plan.
//
// Layout: input is row-major [n rows × width cols]. Element (row=i, col=j)
// lives at data[i*width + j]. Plonky3 transforms each column independently as
// a length-n NTT.
// ============================================================================

/// Compute forward NTT on BabyBear field elements as a batch of `width` columns.
///
/// # Arguments
/// * `data` - Pointer to row-major array of `n * width` u32 values
/// * `n` - NTT size per column (must be power of 2)
/// * `width` - Number of columns (batch size, must be > 0)
///
/// # Returns
/// * 0 on success, -1 on error (null pointer, invalid n/width, overflow, panic)
///
/// # Safety
/// * `data` must point to a valid array of at least `n * width` u32 values
#[no_mangle]
pub unsafe extern "C" fn plonky3_babybear_ntt_forward_batch(
    data: *mut u32,
    n: usize,
    width: usize,
) -> i32 {
    if data.is_null() || n == 0 || (n & (n - 1)) != 0 || width == 0 {
        return -1;
    }
    let total = match n.checked_mul(width) {
        Some(t) => t,
        None => return -1,
    };

    let result = catch_unwind(|| {
        let slice = slice::from_raw_parts_mut(data, total);
        let values: Vec<BabyBear> = slice.iter().map(|&x| BabyBear::new(x)).collect();
        let mat = RowMajorMatrix::new(values, width);
        let dft: Radix2Dit<BabyBear> = Radix2Dit::default();
        let result = dft.dft_batch(mat);
        for (i, v) in result.values.iter().enumerate() {
            slice[i] = PrimeField32::as_canonical_u32(v);
        }
    });

    match result {
        Ok(_) => 0,
        Err(_) => -1,
    }
}

/// Compute forward NTT on KoalaBear field elements as a batch of `width` columns.
///
/// See `plonky3_babybear_ntt_forward_batch` for layout and semantics.
///
/// # Safety
/// * `data` must point to a valid array of at least `n * width` u32 values
#[no_mangle]
pub unsafe extern "C" fn plonky3_koalabear_ntt_forward_batch(
    data: *mut u32,
    n: usize,
    width: usize,
) -> i32 {
    if data.is_null() || n == 0 || (n & (n - 1)) != 0 || width == 0 {
        return -1;
    }
    let total = match n.checked_mul(width) {
        Some(t) => t,
        None => return -1,
    };

    let result = catch_unwind(|| {
        let slice = slice::from_raw_parts_mut(data, total);
        let values: Vec<KoalaBear> = slice.iter().map(|&x| KoalaBear::new(x)).collect();
        let mat = RowMajorMatrix::new(values, width);
        let dft: Radix2Dit<KoalaBear> = Radix2Dit::default();
        let result = dft.dft_batch(mat);
        for (i, v) in result.values.iter().enumerate() {
            slice[i] = PrimeField32::as_canonical_u32(v);
        }
    });

    match result {
        Ok(_) => 0,
        Err(_) => -1,
    }
}

/// Compute forward NTT on Goldilocks field elements as a batch of `width` columns.
///
/// See `plonky3_babybear_ntt_forward_batch` for layout and semantics. Note
/// Goldilocks does NOT vectorize on ARM NEON (no native u64 multiply-high), so
/// width > 1 here measures Radix2DitParallel and cache layout effects only.
///
/// # Safety
/// * `data` must point to a valid array of at least `n * width` u64 values
#[no_mangle]
pub unsafe extern "C" fn plonky3_goldilocks_ntt_forward_batch(
    data: *mut u64,
    n: usize,
    width: usize,
) -> i32 {
    if data.is_null() || n == 0 || (n & (n - 1)) != 0 || width == 0 {
        return -1;
    }
    let total = match n.checked_mul(width) {
        Some(t) => t,
        None => return -1,
    };

    let result = catch_unwind(|| {
        let slice = slice::from_raw_parts_mut(data, total);
        let values: Vec<Goldilocks> = slice.iter().map(|&x| Goldilocks::new(x)).collect();
        let mat = RowMajorMatrix::new(values, width);
        let dft = Radix2Dit::default();
        let result = dft.dft_batch(mat);
        for (i, v) in result.values.iter().enumerate() {
            slice[i] = v.as_canonical_u64();
        }
    });

    match result {
        Ok(_) => 0,
        Err(_) => -1,
    }
}

// ============================================================================
// Debug/Test Functions
// ============================================================================

/// Perform a single field multiplication and return the result.
///
/// Useful for verifying field arithmetic compatibility.
///
/// # Arguments
/// * `a` - First operand
/// * `b` - Second operand
///
/// # Returns
/// * (a * b) mod p
#[no_mangle]
pub extern "C" fn plonky3_mul(a: u64, b: u64) -> u64 {
    let fa = Goldilocks::new(a);
    let fb = Goldilocks::new(b);
    (fa * fb).as_canonical_u64()
}

/// Perform a single field addition and return the result.
///
/// # Arguments
/// * `a` - First operand
/// * `b` - Second operand
///
/// # Returns
/// * (a + b) mod p
#[no_mangle]
pub extern "C" fn plonky3_add(a: u64, b: u64) -> u64 {
    let fa = Goldilocks::new(a);
    let fb = Goldilocks::new(b);
    (fa + fb).as_canonical_u64()
}

/// Perform a single field subtraction and return the result.
///
/// # Arguments
/// * `a` - First operand
/// * `b` - Second operand
///
/// # Returns
/// * (a - b) mod p
#[no_mangle]
pub extern "C" fn plonky3_sub(a: u64, b: u64) -> u64 {
    let fa = Goldilocks::new(a);
    let fb = Goldilocks::new(b);
    (fa - fb).as_canonical_u64()
}

/// Get version information.
///
/// # Returns
/// Version number as: major * 10000 + minor * 100 + patch
/// e.g., 0.1.0 = 100
#[no_mangle]
pub extern "C" fn plonky3_shim_version() -> u32 {
    // 0.1.0
    100
}

// ============================================================================
// Hardening Test Functions
// ============================================================================

/// No-op function for FFI overhead measurement.
/// Does absolutely nothing - used to measure pure FFI call cost.
#[no_mangle]
pub extern "C" fn plonky3_noop() {
    // Intentionally empty
}

/// Intentionally trigger a panic for testing panic safety.
/// With panic="abort" in Cargo.toml, this should cause SIGABRT.
/// WITHOUT panic="abort", this would be Undefined Behavior (UB).
///
/// # Arguments
/// * `trigger` - If non-zero, triggers a panic
///
/// # Returns
/// * 0 if trigger is 0
/// * Never returns if trigger is non-zero (aborts)
#[no_mangle]
pub extern "C" fn plonky3_test_panic(trigger: i32) -> i32 {
    if trigger != 0 {
        panic!("Intentional panic for testing FFI safety");
    }
    0
}

/// Test structure for ABI/Layout validation.
/// Uses #[repr(C)] for C-compatible layout.
#[repr(C)]
pub struct TestLayout {
    pub byte1: u8,
    pub value: u64,
    pub byte2: u8,
}

/// Get the size of TestLayout structure.
/// This should match sizeof(TestLayout) in C.
#[no_mangle]
pub extern "C" fn plonky3_sizeof_test_layout() -> usize {
    std::mem::size_of::<TestLayout>()
}

/// Get the alignment of TestLayout structure.
#[no_mangle]
pub extern "C" fn plonky3_alignof_test_layout() -> usize {
    std::mem::align_of::<TestLayout>()
}

/// Get offset of 'byte1' field in TestLayout.
#[no_mangle]
pub extern "C" fn plonky3_offsetof_byte1() -> usize {
    // Safe because we're using repr(C)
    0
}

/// Get offset of 'value' field in TestLayout.
#[no_mangle]
pub extern "C" fn plonky3_offsetof_value() -> usize {
    // With repr(C): byte1 at 0, padding to align u64 at 8
    std::mem::offset_of!(TestLayout, value)
}

/// Get offset of 'byte2' field in TestLayout.
#[no_mangle]
pub extern "C" fn plonky3_offsetof_byte2() -> usize {
    std::mem::offset_of!(TestLayout, byte2)
}

/// Verify TestLayout by receiving a pointer, modifying, and returning checksum.
///
/// # Safety
/// * `layout` must point to a valid TestLayout structure
#[no_mangle]
pub unsafe extern "C" fn plonky3_verify_layout(layout: *mut TestLayout) -> u64 {
    if layout.is_null() {
        return u64::MAX;
    }

    let result = catch_unwind(|| {
        let l = &mut *layout;

        // Read original values
        let orig_byte1 = l.byte1;
        let orig_value = l.value;
        let orig_byte2 = l.byte2;

        // Modify values
        l.byte1 = orig_byte1.wrapping_add(1);
        l.value = orig_value.wrapping_add(100);
        l.byte2 = orig_byte2.wrapping_add(2);

        // Return checksum of original values
        (orig_byte1 as u64) ^ orig_value ^ (orig_byte2 as u64)
    });

    match result {
        Ok(checksum) => checksum,
        Err(_) => u64::MAX,
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_prime() {
        assert_eq!(plonky3_goldilocks_prime(), 0xFFFF_FFFF_0000_0001);
    }

    #[test]
    fn test_not_montgomery() {
        assert_eq!(plonky3_is_montgomery(), 0);
    }

    #[test]
    fn test_omega_values() {
        // These should match AMO-Lean's primitiveRoot values
        assert_eq!(plonky3_get_omega(8), 0xbf79143ce60ca966);  // N=256
        assert_eq!(plonky3_get_omega(10), 0x9d8f2ad78bfed972); // N=1024
    }

    #[test]
    fn test_field_ops() {
        // Test basic arithmetic
        assert_eq!(plonky3_add(1, 2), 3);
        assert_eq!(plonky3_mul(2, 3), 6);

        // Test modular behavior
        let p = plonky3_goldilocks_prime();
        assert_eq!(plonky3_add(p - 1, 2), 1); // (p-1) + 2 = p + 1 ≡ 1 (mod p)
    }

    #[test]
    fn test_ntt_roundtrip() {
        let mut data = [1u64, 2, 3, 4, 5, 6, 7, 8];
        let original = data.clone();

        unsafe {
            let ret = plonky3_ntt_forward(data.as_mut_ptr(), 8);
            assert_eq!(ret, 0);

            let ret = plonky3_ntt_inverse(data.as_mut_ptr(), 8);
            assert_eq!(ret, 0);
        }

        assert_eq!(data, original);
    }

    #[test]
    fn test_ntt_invalid_input() {
        unsafe {
            // Null pointer
            assert_eq!(plonky3_ntt_forward(std::ptr::null_mut(), 8), -1);

            // Non-power-of-2
            let mut data = [1u64, 2, 3];
            assert_eq!(plonky3_ntt_forward(data.as_mut_ptr(), 3), -1);

            // Zero length
            assert_eq!(plonky3_ntt_forward(data.as_mut_ptr(), 0), -1);
        }
    }

    // ============================================================================
    // Batch NTT tests (v3.19 N319.2.1)
    // ============================================================================

    #[test]
    fn test_babybear_batch_width_one_matches_single() {
        // width=1 batch must produce the same output as the single-vector function.
        let n = 16usize;
        let template: Vec<u32> = (0..n as u32).map(|i| (i * 31 + 7) % BABYBEAR_PRIME).collect();
        let mut single = template.clone();
        let mut batch = template.clone();

        unsafe {
            assert_eq!(plonky3_babybear_ntt_forward(single.as_mut_ptr(), n), 0);
            assert_eq!(
                plonky3_babybear_ntt_forward_batch(batch.as_mut_ptr(), n, 1),
                0
            );
        }
        assert_eq!(single, batch, "width=1 batch must equal single-vector NTT");
    }

    #[test]
    fn test_babybear_batch_width_two_independent_columns() {
        // Two columns batched together must equal two independent NTTs.
        let n = 8usize;
        let col_a: Vec<u32> = (0..n as u32).map(|i| (i + 1) % BABYBEAR_PRIME).collect();
        let col_b: Vec<u32> = (0..n as u32).map(|i| (i * 17 + 3) % BABYBEAR_PRIME).collect();

        // Independent: NTT each column alone.
        let mut indep_a = col_a.clone();
        let mut indep_b = col_b.clone();
        unsafe {
            assert_eq!(plonky3_babybear_ntt_forward(indep_a.as_mut_ptr(), n), 0);
            assert_eq!(plonky3_babybear_ntt_forward(indep_b.as_mut_ptr(), n), 0);
        }

        // Batched: interleave row-major [a0,b0, a1,b1, ...] with width=2.
        let mut interleaved: Vec<u32> = Vec::with_capacity(n * 2);
        for i in 0..n {
            interleaved.push(col_a[i]);
            interleaved.push(col_b[i]);
        }
        unsafe {
            assert_eq!(
                plonky3_babybear_ntt_forward_batch(interleaved.as_mut_ptr(), n, 2),
                0
            );
        }

        // De-interleave and compare.
        for i in 0..n {
            assert_eq!(
                interleaved[i * 2],
                indep_a[i],
                "column 0 mismatch at row {}",
                i
            );
            assert_eq!(
                interleaved[i * 2 + 1],
                indep_b[i],
                "column 1 mismatch at row {}",
                i
            );
        }
    }

    #[test]
    fn test_goldilocks_batch_width_one_matches_single() {
        let n = 16usize;
        let template: Vec<u64> = (0..n as u64).map(|i| i * 1000003 + 5).collect();
        let mut single = template.clone();
        let mut batch = template.clone();

        unsafe {
            assert_eq!(plonky3_ntt_forward(single.as_mut_ptr(), n), 0);
            assert_eq!(
                plonky3_goldilocks_ntt_forward_batch(batch.as_mut_ptr(), n, 1),
                0
            );
        }
        assert_eq!(single, batch, "width=1 batch must equal single-vector NTT");
    }

    #[test]
    fn test_batch_invalid_input() {
        unsafe {
            // Null pointer
            assert_eq!(
                plonky3_babybear_ntt_forward_batch(std::ptr::null_mut(), 8, 4),
                -1
            );
            // n=0
            let mut d32 = [1u32, 2, 3, 4];
            assert_eq!(
                plonky3_babybear_ntt_forward_batch(d32.as_mut_ptr(), 0, 4),
                -1
            );
            // non-power-of-2 n
            assert_eq!(
                plonky3_babybear_ntt_forward_batch(d32.as_mut_ptr(), 3, 1),
                -1
            );
            // width=0
            assert_eq!(
                plonky3_babybear_ntt_forward_batch(d32.as_mut_ptr(), 4, 0),
                -1
            );
            // n*width overflow
            assert_eq!(
                plonky3_babybear_ntt_forward_batch(d32.as_mut_ptr(), 1usize << 40, 1usize << 40),
                -1
            );
        }
    }
}
