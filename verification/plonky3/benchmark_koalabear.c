/*
 * Plonky3 Real KoalaBear NTT Benchmark
 *
 * Measures actual Plonky3 (monty-31 + NEON) NTT performance for KoalaBear.
 * Links against libplonky3_shim which calls Plonky3's Radix2Dit directly.
 *
 * Output: CSV line per (field, logN) with timing in microseconds.
 * Format: field,log_n,n,p3_real_us,melem_s
 *
 * Usage:
 *   make benchmark_koalabear
 *   ./benchmark_koalabear [log_n_min] [log_n_max] [iters]
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <dlfcn.h>

#define KOALABEAR_P 2130706433U

typedef int (*ntt_fn)(uint32_t* data, size_t len);
typedef uint32_t (*prime_fn)(void);

static double time_ms(struct timespec *start, struct timespec *end) {
    return (end->tv_sec - start->tv_sec) * 1000.0 +
           (end->tv_nsec - start->tv_nsec) / 1e6;
}

static void init_data(uint32_t *data, size_t n) {
    for (size_t i = 0; i < n; i++) {
        data[i] = (uint32_t)(((uint64_t)i * 1000000007ULL) % KOALABEAR_P);
    }
}

int main(int argc, char **argv) {
    int log_n_min = (argc > 1) ? atoi(argv[1]) : 14;
    int log_n_max = (argc > 2) ? atoi(argv[2]) : 22;
    int iters     = (argc > 3) ? atoi(argv[3]) : 10;

    void *lib = dlopen("plonky3_shim/target/release/libplonky3_shim.dylib", RTLD_NOW);
    if (!lib) lib = dlopen("plonky3_shim/target/release/libplonky3_shim.so", RTLD_NOW);
    if (!lib) {
        fprintf(stderr, "ERROR: Cannot load plonky3_shim: %s\n", dlerror());
        return 1;
    }

    ntt_fn p3_ntt = (ntt_fn)dlsym(lib, "plonky3_koalabear_ntt_forward");
    prime_fn p3_prime = (prime_fn)dlsym(lib, "plonky3_koalabear_prime");

    if (!p3_ntt || !p3_prime) {
        fprintf(stderr, "ERROR: Cannot find KoalaBear symbols: %s\n", dlerror());
        dlclose(lib);
        return 1;
    }

    uint32_t p = p3_prime();
    if (p != KOALABEAR_P) {
        fprintf(stderr, "ERROR: Prime mismatch: expected %u, got %u\n", KOALABEAR_P, p);
        dlclose(lib);
        return 1;
    }

    printf("# Plonky3 Real KoalaBear NTT Benchmark\n");
    printf("# Plonky3 Radix2Dit via FFI (monty-31, compiled with release+lto)\n");
    printf("# Platform: aarch64, iters=%d\n", iters);
    printf("# field,log_n,n,p3_real_us,melem_s\n");

    for (int log_n = log_n_min; log_n <= log_n_max; log_n += 2) {
        size_t n = (size_t)1 << log_n;
        uint32_t *data = (uint32_t *)malloc(n * sizeof(uint32_t));
        uint32_t *backup = (uint32_t *)malloc(n * sizeof(uint32_t));
        if (!data || !backup) {
            fprintf(stderr, "ERROR: malloc failed for N=2^%d\n", log_n);
            continue;
        }

        init_data(backup, n);

        /* Warmup */
        for (int w = 0; w < 2; w++) {
            memcpy(data, backup, n * sizeof(uint32_t));
            p3_ntt(data, n);
        }

        /* Timed runs */
        double total_us = 0;
        for (int it = 0; it < iters; it++) {
            memcpy(data, backup, n * sizeof(uint32_t));
            struct timespec t0, t1;
            clock_gettime(CLOCK_MONOTONIC, &t0);
            int ret = p3_ntt(data, n);
            clock_gettime(CLOCK_MONOTONIC, &t1);
            if (ret != 0) {
                fprintf(stderr, "ERROR: NTT failed for N=2^%d iter=%d\n", log_n, it);
                break;
            }
            total_us += time_ms(&t0, &t1) * 1000.0;
        }

        double avg_us = total_us / iters;
        double melem = (double)n / avg_us;
        printf("koalabear,%d,%zu,%.1f,%.1f\n", log_n, n, avg_us, melem);
        fflush(stdout);

        free(data);
        free(backup);
    }

    dlclose(lib);
    return 0;
}
