#!/bin/bash
# run_sanitizer_tests.sh - Run tests with Address Sanitizer and Undefined Behavior Sanitizer
#
# This script compiles and runs the Goldilocks tests with sanitizers enabled
# to detect memory errors and undefined behavior.
#
# Usage: ./run_sanitizer_tests.sh

set -e

echo "╔══════════════════════════════════════════════════════════════╗"
echo "║     SANITIZER TESTS: ASan + UBSan                            ║"
echo "╚══════════════════════════════════════════════════════════════╝"
echo ""

cd "$(dirname "$0")"

# Compiler flags for sanitizers
SANITIZER_FLAGS="-fsanitize=address,undefined -fno-omit-frame-pointer -g"
COMMON_FLAGS="-O1 -Wall -Wextra"

echo "=== Compiling with sanitizers ==="
echo "Flags: $SANITIZER_FLAGS $COMMON_FLAGS"
echo ""

# Compile Goldilocks tests with sanitizers
echo "Compiling test_goldilocks_sanitized..."
gcc $SANITIZER_FLAGS $COMMON_FLAGS -o test_goldilocks_sanitized test_goldilocks.c 2>&1

if [ $? -ne 0 ]; then
    echo "❌ Compilation failed!"
    exit 1
fi
echo "✅ Compilation successful"
echo ""

# Run the sanitized tests
echo "=== Running Goldilocks tests with sanitizers ==="
echo ""

# Set ASan options (detect_leaks not supported on macOS)
export ASAN_OPTIONS="abort_on_error=0:print_stacktrace=1"
export UBSAN_OPTIONS="print_stacktrace=1:halt_on_error=0"

./test_goldilocks_sanitized

RESULT=$?

echo ""
if [ $RESULT -eq 0 ]; then
    echo "════════════════════════════════════════════════════════════════"
    echo "SANITIZER TESTS PASSED ✅"
    echo "No memory errors or undefined behavior detected."
    echo "════════════════════════════════════════════════════════════════"
else
    echo "════════════════════════════════════════════════════════════════"
    echo "SANITIZER TESTS FAILED ❌"
    echo "Memory errors or undefined behavior detected!"
    echo "════════════════════════════════════════════════════════════════"
fi

# Cleanup
rm -f test_goldilocks_sanitized

exit $RESULT
