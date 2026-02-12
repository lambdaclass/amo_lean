# verification/plonky3/Makefile
#
# Build orchestrator for Plonky3 verification suite
# Phase 6A: AMO-Lean as Plonky3 Verifier

CC = gcc
CFLAGS = -O3 -Wall -Wextra -I../../generated
LDFLAGS = -ldl -lm

# Detect OS for library extension
UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S),Darwin)
    LIB_EXT = dylib
    RPATH_FLAG = -Wl,-rpath,@executable_path/plonky3_shim/target/release
else
    LIB_EXT = so
    RPATH_FLAG = -Wl,-rpath,'$$ORIGIN/plonky3_shim/target/release'
endif

SHIM_LIB = plonky3_shim/target/release/libplonky3_shim.$(LIB_EXT)

.PHONY: all clean shim test oracle benchmark help

# Default target
all: shim shim_test

# Help
help:
	@echo "═══════════════════════════════════════════════════════════"
	@echo "  Plonky3 Verification Suite - Phase 6A"
	@echo "═══════════════════════════════════════════════════════════"
	@echo ""
	@echo "Targets:"
	@echo "  all        - Build shim and basic test"
	@echo "  shim       - Build Rust shim (libplonky3_shim)"
	@echo "  test       - Run shim loading test"
	@echo "  oracle     - Build and run oracle tests (6A.4)"
	@echo "  benchmark  - Build and run benchmarks (6A.5)"
	@echo "  clean      - Remove all build artifacts"
	@echo ""

# Build Rust shim
shim: $(SHIM_LIB)

$(SHIM_LIB): plonky3_shim/Cargo.toml plonky3_shim/src/lib.rs
	@echo "Building Plonky3 shim..."
	cd plonky3_shim && cargo build --release
	@echo "Shim built: $(SHIM_LIB)"

# Build shim test
shim_test: shim_test.c $(SHIM_LIB)
	$(CC) $(CFLAGS) -o $@ $< $(LDFLAGS) $(RPATH_FLAG)

# Run tests
test: shim_test
	@echo ""
	./shim_test

# Run Rust tests
test-rust:
	cd plonky3_shim && cargo test --release

# Oracle test (to be implemented in 6A.4)
oracle: oracle_test
	./oracle_test

oracle_test: oracle_test.c $(SHIM_LIB)
	$(CC) $(CFLAGS) -o $@ $< $(LDFLAGS) $(RPATH_FLAG)

# Benchmark (to be implemented in 6A.5)
benchmark: benchmark_test
	./benchmark_test

benchmark_test: benchmark.c $(SHIM_LIB)
	$(CC) $(CFLAGS) -o $@ $< $(LDFLAGS) $(RPATH_FLAG)

# Clean
clean:
	rm -f shim_test oracle_test benchmark_test
	cd plonky3_shim && cargo clean

# Show library info
info:
	@echo "Library: $(SHIM_LIB)"
	@echo "Symbols:"
	@nm -gU $(SHIM_LIB) 2>/dev/null | grep plonky3 || echo "(not built yet)"
