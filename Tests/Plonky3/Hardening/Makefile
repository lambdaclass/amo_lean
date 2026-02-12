# Tests/Plonky3/Hardening/Makefile
#
# Build and run Phase 6A Hardening Tests

CC = gcc
CFLAGS = -O2 -Wall -Wextra -std=c11 -I../../../generated -I../../../verification/plonky3
LDFLAGS = -ldl -lm

# Paths
SHIM_DIR = ../../../verification/plonky3/plonky3_shim
SHIM_LIB = $(SHIM_DIR)/target/release/libplonky3_shim.dylib
BENCH_DIR = ../Bench

# Detect OS
UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S),Darwin)
    LIB_EXT = dylib
else
    LIB_EXT = so
    CFLAGS += -D_POSIX_C_SOURCE=199309L
endif

.PHONY: all clean shim test stress panic deepfuzz layout bench valgrind report

# Default: build all tests
all: ffi_stress panic_test deep_fuzz layout_test ffi_overhead

# Build shim first
shim:
	cd $(SHIM_DIR) && cargo build --release

# Individual test builds
ffi_stress: FFI_Stress.c | shim
	$(CC) $(CFLAGS) -o $@ $< $(LDFLAGS)

panic_test: PanicTest.c | shim
	$(CC) $(CFLAGS) -o $@ $< $(LDFLAGS)

deep_fuzz: DeepFuzz.c | shim
	$(CC) $(CFLAGS) -o $@ $< $(LDFLAGS)

layout_test: LayoutTest.c | shim
	$(CC) $(CFLAGS) -o $@ $< $(LDFLAGS)

ffi_overhead: $(BENCH_DIR)/FFI_Overhead.c | shim
	$(CC) $(CFLAGS) -o $@ $< $(LDFLAGS)

# Run tests individually
stress: ffi_stress
	@echo ""
	@echo "Running FFI Stress Test..."
	@cd ../../../verification/plonky3 && $(CURDIR)/ffi_stress

panic: panic_test
	@echo ""
	@echo "Running Panic Safety Test (defensive mode)..."
	@cd ../../../verification/plonky3 && $(CURDIR)/panic_test defensive

panic-trigger: panic_test
	@echo ""
	@echo "Running Panic Safety Test (trigger mode)..."
	@cd ../../../verification/plonky3 && $(CURDIR)/panic_test trigger

deepfuzz: deep_fuzz
	@echo ""
	@echo "Running Deep Fuzz Test..."
	@cd ../../../verification/plonky3 && $(CURDIR)/deep_fuzz

layout: layout_test
	@echo ""
	@echo "Running Layout Test..."
	@cd ../../../verification/plonky3 && $(CURDIR)/layout_test

bench: ffi_overhead
	@echo ""
	@echo "Running FFI Overhead Benchmark..."
	@cd ../../../verification/plonky3 && $(CURDIR)/ffi_overhead

# Run with Valgrind (Linux only, or with Docker on macOS)
valgrind: ffi_stress
	@echo ""
	@echo "Running FFI Stress Test under Valgrind..."
	@cd ../../../verification/plonky3 && valgrind \
		--leak-check=full \
		--show-leak-kinds=all \
		--error-exitcode=1 \
		--track-origins=yes \
		$(CURDIR)/ffi_stress 2>&1 | tee valgrind_report.txt
	@echo ""
	@echo "Valgrind report saved to valgrind_report.txt"

# Run all tests
test: all stress panic deepfuzz layout bench
	@echo ""
	@echo "═══════════════════════════════════════════════════════════════"
	@echo "  ALL HARDENING TESTS COMPLETED"
	@echo "═══════════════════════════════════════════════════════════════"

# Generate report
report: test
	@echo ""
	@echo "Generating hardening report..."
	@date > hardening_report.txt
	@echo "" >> hardening_report.txt
	@echo "=== FFI Stress Test ===" >> hardening_report.txt
	@cd ../../../verification/plonky3 && $(CURDIR)/ffi_stress >> $(CURDIR)/hardening_report.txt 2>&1
	@echo "" >> hardening_report.txt
	@echo "=== Panic Safety Test ===" >> hardening_report.txt
	@cd ../../../verification/plonky3 && $(CURDIR)/panic_test defensive >> $(CURDIR)/hardening_report.txt 2>&1
	@echo "" >> hardening_report.txt
	@echo "=== Deep Fuzz Test ===" >> hardening_report.txt
	@cd ../../../verification/plonky3 && $(CURDIR)/deep_fuzz >> $(CURDIR)/hardening_report.txt 2>&1
	@echo "" >> hardening_report.txt
	@echo "=== Layout Test ===" >> hardening_report.txt
	@cd ../../../verification/plonky3 && $(CURDIR)/layout_test >> $(CURDIR)/hardening_report.txt 2>&1
	@echo "" >> hardening_report.txt
	@echo "=== FFI Overhead ===" >> hardening_report.txt
	@cd ../../../verification/plonky3 && $(CURDIR)/ffi_overhead >> $(CURDIR)/hardening_report.txt 2>&1
	@echo ""
	@echo "Report saved to hardening_report.txt"

# Clean
clean:
	rm -f ffi_stress panic_test deep_fuzz layout_test ffi_overhead
	rm -f hardening_report.txt valgrind_report.txt

# Help
help:
	@echo "Phase 6A Hardening Test Suite"
	@echo ""
	@echo "Targets:"
	@echo "  all        - Build all tests"
	@echo "  test       - Run all tests"
	@echo "  stress     - Run FFI stress test (1M iterations)"
	@echo "  panic      - Run panic safety test (defensive)"
	@echo "  panic-trigger - Run panic safety test (trigger panic)"
	@echo "  deepfuzz   - Run deep fuzz with pathological vectors"
	@echo "  layout     - Run ABI layout verification"
	@echo "  bench      - Run FFI overhead benchmark"
	@echo "  valgrind   - Run stress test under Valgrind"
	@echo "  report     - Generate full hardening report"
	@echo "  clean      - Remove built files"
