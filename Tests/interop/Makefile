# Tests/interop/Makefile
#
# B94: Comprehensive Interoperability Test Suite
# Validates AMO-Lean generated C code (field ops, NTT, etc.)

CC = clang
CFLAGS = -O2 -Wall -Wextra -I../../generated
LDFLAGS =

# Suppress unused-function warnings from header-only libraries
CFLAGS += -Wno-unused-function

.PHONY: all test clean

all: test_comprehensive

test_comprehensive: test_comprehensive.c
	$(CC) $(CFLAGS) -o $@ $< $(LDFLAGS)

test: test_comprehensive
	@echo ""
	@echo "Running comprehensive interop tests..."
	@echo ""
	./test_comprehensive

clean:
	rm -f test_comprehensive
