# Poseidon2 S-box Tests Makefile
#
# Targets:
#   all          - Build all tests and benchmarks
#   test         - Run correctness tests
#   benchmark    - Run performance benchmarks
#   hygiene      - Compile with strict warning flags (Test 2.4)
#   asan         - Compile with AddressSanitizer (Test 2.5)
#   clean        - Remove build artifacts

CC = clang
CFLAGS_BASE = -std=c99 -O2

# Standard flags
CFLAGS = $(CFLAGS_BASE) -g

# Hygiene flags (Test 2.4: Compilation Hygiene)
CFLAGS_HYGIENE = $(CFLAGS_BASE) -Wall -Wextra -Werror -pedantic \
    -Wconversion -Wsign-conversion -Wcast-align -Wstrict-prototypes \
    -Wmissing-prototypes -Wold-style-definition -Wformat=2 \
    -Wno-unused-parameter

# ASAN flags (Test 2.5: Memory Safety)
# Note: -fsanitize=leak not supported on macOS ARM
CFLAGS_ASAN = $(CFLAGS_BASE) -g -fsanitize=address -fno-omit-frame-pointer \
    -fsanitize=undefined

LDFLAGS_ASAN = -fsanitize=address -fsanitize=undefined

SRCS = bn254_field.c
OBJS = $(SRCS:.c=.o)

# Build directory
BUILD_DIR = build

.PHONY: all test benchmark hygiene asan clean dirs differential testvector phase4

all: dirs $(BUILD_DIR)/test_sbox $(BUILD_DIR)/benchmark $(BUILD_DIR)/test_differential $(BUILD_DIR)/test_vector

dirs:
	@mkdir -p $(BUILD_DIR)

# Standard build
$(BUILD_DIR)/bn254_field.o: bn254_field.c bn254_field.h
	$(CC) $(CFLAGS) -c $< -o $@

$(BUILD_DIR)/test_sbox: test_sbox.c $(BUILD_DIR)/bn254_field.o
	$(CC) $(CFLAGS) $^ -o $@

$(BUILD_DIR)/benchmark: benchmark.c $(BUILD_DIR)/bn254_field.o
	$(CC) $(CFLAGS) $^ -o $@

$(BUILD_DIR)/test_differential: test_differential.c $(BUILD_DIR)/bn254_field.o
	$(CC) $(CFLAGS) $^ -o $@

$(BUILD_DIR)/test_vector: test_vector.c $(BUILD_DIR)/bn254_field.o
	$(CC) $(CFLAGS) -I../../generated $^ -o $@

# Hygiene build (strict warnings)
$(BUILD_DIR)/bn254_field_hygiene.o: bn254_field.c bn254_field.h
	@echo "══════ Test 2.4: Compilation Hygiene ══════"
	@echo "Compiling with: $(CFLAGS_HYGIENE)"
	$(CC) $(CFLAGS_HYGIENE) -c $< -o $@

$(BUILD_DIR)/test_sbox_hygiene: test_sbox.c $(BUILD_DIR)/bn254_field_hygiene.o
	$(CC) $(CFLAGS_HYGIENE) $^ -o $@
	@echo "✓ Compilation hygiene PASSED - no warnings"

hygiene: dirs $(BUILD_DIR)/test_sbox_hygiene

# ASAN build (memory safety)
$(BUILD_DIR)/bn254_field_asan.o: bn254_field.c bn254_field.h
	$(CC) $(CFLAGS_ASAN) -c $< -o $@

$(BUILD_DIR)/test_sbox_asan: test_sbox.c $(BUILD_DIR)/bn254_field_asan.o
	@echo "══════ Test 2.5: AddressSanitizer Build ══════"
	$(CC) $(CFLAGS_ASAN) $(LDFLAGS_ASAN) $^ -o $@

$(BUILD_DIR)/benchmark_asan: benchmark.c $(BUILD_DIR)/bn254_field_asan.o
	$(CC) $(CFLAGS_ASAN) $(LDFLAGS_ASAN) $^ -o $@

asan: dirs $(BUILD_DIR)/test_sbox_asan $(BUILD_DIR)/benchmark_asan
	@echo ""
	@echo "══════ Running tests with AddressSanitizer ══════"
	$(BUILD_DIR)/test_sbox_asan
	@echo ""
	@echo "✓ ASAN tests PASSED - no memory errors detected"

# Run tests
test: all
	@echo ""
	@echo "══════════════════════════════════════════════════════════════════"
	@echo "  Running Correctness Tests (Test 2.1, 2.2)"
	@echo "══════════════════════════════════════════════════════════════════"
	@echo ""
	$(BUILD_DIR)/test_sbox

# Run benchmarks
benchmark: all
	@echo ""
	@echo "══════════════════════════════════════════════════════════════════"
	@echo "  Running Performance Benchmarks (Benchmark 2.1)"
	@echo "══════════════════════════════════════════════════════════════════"
	@echo ""
	$(BUILD_DIR)/benchmark 100000

# Run Phase 4a test vector validation
testvector: all
	@echo ""
	@echo "══════════════════════════════════════════════════════════════════"
	@echo "  Phase 4a: Test Vector Validation (HorizenLabs reference)"
	@echo "══════════════════════════════════════════════════════════════════"
	@echo ""
	$(BUILD_DIR)/test_vector

# Run differential fuzzing
differential: all
	@echo ""
	@echo "══════════════════════════════════════════════════════════════════"
	@echo "  Running Differential Fuzzing Tests (Test 2.3)"
	@echo "══════════════════════════════════════════════════════════════════"
	@echo ""
	$(BUILD_DIR)/test_differential

# Phase 4 complete test suite
phase4: all testvector test differential
	@echo ""
	@echo "══════════════════════════════════════════════════════════════════"
	@echo "  PHASE 4 TEST SUITE COMPLETED"
	@echo "══════════════════════════════════════════════════════════════════"

# Full test suite
fulltest: hygiene asan test differential benchmark testvector
	@echo ""
	@echo "══════════════════════════════════════════════════════════════════"
	@echo "  FULL TEST SUITE COMPLETED"
	@echo "══════════════════════════════════════════════════════════════════"

clean:
	rm -rf $(BUILD_DIR)

# Help
help:
	@echo "Poseidon2 S-box Test Suite"
	@echo ""
	@echo "Targets:"
	@echo "  make all       - Build all tests"
	@echo "  make test      - Run correctness tests (Test 2.1, 2.2)"
	@echo "  make hygiene   - Compile with strict warnings (Test 2.4)"
	@echo "  make asan      - Run tests with AddressSanitizer (Test 2.5)"
	@echo "  make benchmark - Run performance benchmarks (Benchmark 2.1)"
	@echo "  make fulltest  - Run complete test suite"
	@echo "  make clean     - Remove build artifacts"
