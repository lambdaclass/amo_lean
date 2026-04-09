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
use p3_field::{PrimeField64, TwoAdicField};
use p3_goldilocks::Goldilocks;
use p3_matrix::dense::RowMajorMatrix;

/// Goldilocks prime: p = 2^64 - 2^32 + 1
const GOLDILOCKS_PRIME: u64 = 0xFFFF_FFFF_0000_0001;

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
}
