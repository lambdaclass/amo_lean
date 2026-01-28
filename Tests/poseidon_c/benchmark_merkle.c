/**
 * Poseidon2 Integration Benchmark - Step 5.1 Performance Tax
 *
 * Compares:
 *   - XOR-based hash (testHash from Merkle.lean)
 *   - Poseidon2 BN254 hash (poseidon2MerkleHash)
 *
 * Measures:
 *   - Single hash latency
 *   - Merkle tree construction time (8, 64, 256, 1024, 16384 leaves)
 *   - Slowdown factor
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include "bn254_field.h"

// Golden ratio constant for XOR mixing (from Merkle.lean)
#define GOLDEN_RATIO 0x9e3779b97f4a7c15ULL

/* ============================================================================
 * Round Constants (same as in runner_fuzz.c)
 * ============================================================================ */

static const uint64_t RC_3[64][3][4] = {
    // Round 0-3 (full rounds)
    {{0x59a09a1a97052816ULL, 0x7f8fcde48bb4c37aULL, 0x8bddd3a93f7804efULL, 0x1d066a255517b7fdULL},
     {0xb7238547d32c1610ULL, 0xb7c6fef31367b68eULL, 0xac3f089cebcc6120ULL, 0x29daefb55f6f2dc6ULL},
     {0x9e8b7ad7b0b4e1d1ULL, 0x2572d76f08ec5c4fULL, 0x1ecbd88ad959d701ULL, 0x1f2cb1624a78ee00ULL}},
    {{0xdb0672ded84f31e5ULL, 0xb11f092a53bbc6e1ULL, 0xbd77c0ed3d14aa27ULL, 0x0aad2e79f15735f2ULL},
     {0x091ccf1595b43f28ULL, 0x37028a98f1dece66ULL, 0xd6f661dd4094375fULL, 0x2252624f8617738cULL},
     {0xd49f4f2c9018d735ULL, 0x91c20626524b2b87ULL, 0x5a65a84a291da1ffULL, 0x1a24913a928b3848ULL}},
    {{0x4fd6dae1508fc47aULL, 0x0a41515ddff497b1ULL, 0x7bfc427b5f11ebb1ULL, 0x22fc468f1759b74dULL},
     {0xefd65515617f6e4dULL, 0xe61956ff0b4121d5ULL, 0x9cd026e9c9ca107aULL, 0x1059ca787f1f89edULL},
     {0xa45cbbfae8b981ceULL, 0x2123011f0bf6f155ULL, 0xf61f3536d877de98ULL, 0x02be9473358461d8ULL}},
    {{0xa1ff3a441a5084a4ULL, 0xaba9b669ac5b8736ULL, 0x2778a749c82ed623ULL, 0x0ec96c8e32962d46ULL},
     {0x48fb2e4d814df57eULL, 0x5a47a7cdb8c99f96ULL, 0x5442d9553c45fa3fULL, 0x292f906e07367740ULL},
     {0x0c63f0b2ffe5657eULL, 0xcc611160a394ea46ULL, 0x26c11b9a0f5e39a5ULL, 0x274982444157b867ULL}},
    // Rounds 4-59: partial (56 rounds)
    {{0x499573f23597d4b5ULL, 0xcedd192f47308731ULL, 0xb63e1855bff015b8ULL, 0x1a1d063e54b1e764ULL}, {0}, {0}},
    {{0xb91b002c5b257c37ULL, 0x08235dccc1aa3793ULL, 0x839d109562590637ULL, 0x26abc66f3fdf8e68ULL}, {0}, {0}},
    {{0x0b3c2b12ff4d7be8ULL, 0x0754427aabca92a7ULL, 0x81a578cfed5aed37ULL, 0x0c7c64a9d8873853ULL}, {0}, {0}},
    {{0xedd383831354b495ULL, 0xba2ebac30dc386b0ULL, 0x9e17f0b6d08b2d1eULL, 0x1cf5998769e9fab7ULL}, {0}, {0}},
    {{0x7aba0b97e66b0109ULL, 0x19828764a9669bc1ULL, 0x564ca60461e9e08bULL, 0x0f5e3a8566be31b7ULL}, {0}, {0}},
    {{0x42bf3d7a531c976eULL, 0xf359a53a180b7d4bULL, 0x95e60e4db0794a01ULL, 0x18df6a9d19ea90d8ULL}, {0}, {0}},
    {{0x4e324055fa3123dcULL, 0xd0ea1d3a3b9d25efULL, 0x6e4b782c3c6e601aULL, 0x04f7bf2c5c0538acULL}, {0}, {0}},
    {{0xe55d54628b89ebe6ULL, 0xe770c0584aa2328cULL, 0x3c40058523748531ULL, 0x29c76ce22255206eULL}, {0}, {0}},
    {{0x00e0e945dbc5ff15ULL, 0x65b1b8e9c6108dbeULL, 0xc053659ab4347f5dULL, 0x198d425a45b78e85ULL}, {0}, {0}},
    {{0x49d3a9a90c3fdf74ULL, 0xa7ff7f6878b3c49dULL, 0x6af3cc79c598a1daULL, 0x25ee27ab6296cd5eULL}, {0}, {0}},
    {{0xc0f88687a96d1381ULL, 0x05845d7d0c55b1b2ULL, 0x24561001c0b6eb15ULL, 0x138ea8e0af41a1e0ULL}, {0}, {0}},
    {{0x4013370a01d95687ULL, 0x42851b5b9811f2caULL, 0xf6e7c2cba2eefd0eULL, 0x306197fb3fab671eULL}, {0}, {0}},
    {{0x86419eaf00e8f620ULL, 0x21db7565e5b42504ULL, 0x2b66f0b4894d4f1aULL, 0x1a0c7d52dc32a443ULL}, {0}, {0}},
    {{0xaa52997da2c54a9fULL, 0xebfbe5f55163cd6cULL, 0x3ff86a8e5c8bdfccULL, 0x2b46b418de80915fULL}, {0}, {0}},
    {{0xfb46e312b5829f64ULL, 0x613a1af5db48e05bULL, 0x01f8b777b9673af9ULL, 0x12d3e0dc00858737ULL}, {0}, {0}},
    {{0xba338a5cb19b3a1fULL, 0xfb2bf768230f648dULL, 0x70f5002ed21d089fULL, 0x263390cf74dc3a88ULL}, {0}, {0}},
    {{0x7d543db52b003dcdULL, 0xf8abb5af40f96f1dULL, 0x0ac884b4ca607ad0ULL, 0x0a14f33a5fe668a6ULL}, {0}, {0}},
    {{0xd847df829bc683b9ULL, 0x27be3a4f01171a1dULL, 0x1a5e86509d68b2daULL, 0x28ead9c586513eabULL}, {0}, {0}},
    {{0xea16cda6e1a7416cULL, 0x888f0ea1abe71cffULL, 0x0972031f1bdb2ac9ULL, 0x1c6ab1c328c3c643ULL}, {0}, {0}},
    {{0x32346015c5b42c94ULL, 0x4f6decd608cb98a9ULL, 0x2b2500239f7f8de0ULL, 0x1fc7e71bc0b81979ULL}, {0}, {0}},
    {{0xe6dd85b93a0ddaa8ULL, 0xc0c1e197c952650eULL, 0xe380e0d860298f17ULL, 0x03e107eb3a42b2ecULL}, {0}, {0}},
    {{0x454505f6941d78cdULL, 0x46452ca57c08697fULL, 0x69c0d52bf88b772cULL, 0x2d354a251f381a46ULL}, {0}, {0}},
    {{0xd14b4606826f794bULL, 0x522551d61606eda3ULL, 0xf687ef14bc566d1cULL, 0x094af88ab05d94baULL}, {0}, {0}},
    {{0xd52b2d249d1396f7ULL, 0xe1ab5b6f2e3195a9ULL, 0x19bcaeabf02f8ca5ULL, 0x19705b783bf3d2dcULL}, {0}, {0}},
    {{0x60cef6852271200eULL, 0x8723b16b7d740a3eULL, 0x1fcc33fee54fc5b2ULL, 0x09bf4acc3a8bce3fULL}, {0}, {0}},
    {{0x543a073f3f3b5e4eULL, 0x3413732f301f7058ULL, 0x50f83c0c8fab6284ULL, 0x1803f8200db6013cULL}, {0}, {0}},
    {{0xd41f7fef2faf3e5cULL, 0xbf6fb02d4454c0adULL, 0x30595b160b8d1f38ULL, 0x0f80afb5046244deULL}, {0}, {0}},
    {{0x7dc3f98219529d78ULL, 0xabcfcf643f4a6feaULL, 0xd77f0088c1cfc964ULL, 0x126ee1f8504f15c3ULL}, {0}, {0}},
    {{0xef86f991d7d0a591ULL, 0x0ffb4ee63175ddf8ULL, 0x69bfb3d919552ca1ULL, 0x23c203d10cfcc60fULL}, {0}, {0}},
    {{0x7c5a339f7744fb94ULL, 0x3dec1ee4eec2cf74ULL, 0xec0d09705fa3a630ULL, 0x2a2ae15d8b143709ULL}, {0}, {0}},
    {{0xb6b5d89081970b2bULL, 0xc3d3b3006cb461bbULL, 0x47e5c381ab6343ecULL, 0x07b60dee586ed6efULL}, {0}, {0}},
    {{0x132cfe583c9311bdULL, 0x8a98a320baa7d152ULL, 0x885d95c494c1ae3dULL, 0x27316b559be3edfdULL}, {0}, {0}},
    {{0x2f5f9af0c0342e76ULL, 0xef834cc2a743ed66ULL, 0xd8937cb2d3f84311ULL, 0x1d5c49ba157c32b8ULL}, {0}, {0}},
    {{0x7c24bd5940968488ULL, 0x09c01bf6979938f6ULL, 0x332774e0b850b5ecULL, 0x2f8b124e78163b2fULL}, {0}, {0}},
    {{0x665f75260113b3d5ULL, 0x1d4cba6554e51d84ULL, 0xdc5b7aa09a9ce21bULL, 0x1e6843a5457416b6ULL}, {0}, {0}},
    {{0x1f5bc79f21641d4bULL, 0xa68daf9ac6a189abULL, 0x5fca25c9929c8ad9ULL, 0x11cdf00a35f650c5ULL}, {0}, {0}},
    {{0xe82b5b9b7eb560bcULL, 0x608b2815c77355b7ULL, 0x2ef36e588158d6d4ULL, 0x21632de3d3bbc5e4ULL}, {0}, {0}},
    {{0x49d7b5c51c18498aULL, 0x255ae48ef2a329e4ULL, 0x97b27025fbd245e0ULL, 0x0de625758452efbdULL}, {0}, {0}},
    {{0x9b09546ba0838098ULL, 0xdd9e1e1c6f0fb6b0ULL, 0xe2febfd4d976cc01ULL, 0x2ad253c053e75213ULL}, {0}, {0}},
    {{0xd35702e38d60b077ULL, 0x3dd49cdd13c813b7ULL, 0x6ec7681ec39b3be9ULL, 0x1d6b169ed63872dcULL}, {0}, {0}},
    {{0xc3a54e706cfef7feULL, 0x0be3ea70a24d5568ULL, 0xb9127c4941b67fedULL, 0x1660b740a143664bULL}, {0}, {0}},
    {{0x96a29f10376ccbfeULL, 0xceacdddb12cf8790ULL, 0x114f4ca2deef76e0ULL, 0x0065a92d1de81f34ULL}, {0}, {0}},
    {{0xcf30d50a5871040dULL, 0x353ebe2ccbc4869bULL, 0x7367f823da7d672cULL, 0x1f11f06520253598ULL}, {0}, {0}},
    {{0x110852d17df0693eULL, 0x3bd1d1a39b6759baULL, 0xb437ce7b14a2c3ddULL, 0x26596f5c5dd5a5d1ULL}, {0}, {0}},
    {{0x6743db15af91860fULL, 0x8539c4163a5f1e70ULL, 0x7bf3056efcf8b6d3ULL, 0x16f49bc727e45a2fULL}, {0}, {0}},
    {{0xe1a4e7438dd39e5fULL, 0x568feaf7ea8b3dc5ULL, 0x9954175efb331bf4ULL, 0x1abe1deb45b3e311ULL}, {0}, {0}},
    {{0x020d34aea15fba59ULL, 0x9f5db92aaec5f102ULL, 0xd8993a74ca548b77ULL, 0x0e426ccab66984d1ULL}, {0}, {0}},
    {{0xa841924303f6a6c6ULL, 0x0071684b902d534fULL, 0x4933bd1942053f1fULL, 0x0e7c30c2e2e8957fULL}, {0}, {0}},
    {{0x4c76e1f31d3fc69dULL, 0x6166ded6e3528eadULL, 0x1622708fc7edff1dULL, 0x0812a017ca92cf0aULL}, {0}, {0}},
    {{0x2e276b47cf010d54ULL, 0x68afe5026edd7a9cULL, 0xbba949d1db960400ULL, 0x21a5ade3df2bc1b5ULL}, {0}, {0}},
    {{0x72b1a5233f8749ceULL, 0xbd101945f50e5afeULL, 0xad711bf1a058c6c6ULL, 0x01f3035463816c84ULL}, {0}, {0}},
    {{0x4dcaa82b0f0c1c8bULL, 0x8bf2f9398dbd0fdfULL, 0x028c2aafc2d06a5eULL, 0x0b115572f038c0e2ULL}, {0}, {0}},
    {{0x3460613b6ef59e2fULL, 0x27fc24db42bc910aULL, 0xf0ef255543f50d2eULL, 0x1c38ec0b99b62fd4ULL}, {0}, {0}},
    {{0xb1d0b254d880c53eULL, 0x2f5d314606a297d4ULL, 0x425c3ff1f4ac737bULL, 0x1c89c6d9666272e8ULL}, {0}, {0}},
    {{0x8b71e2311bb88f8fULL, 0x21ad4880097a5eb3ULL, 0xf6d44008ae4c042aULL, 0x03326e643580356bULL}, {0}, {0}},
    {{0x5bdde2299910a4c9ULL, 0x50f27a6434b5dcebULL, 0x67cee9ea0e51e3adULL, 0x268076b0054fb73fULL}, {0}, {0}},
    // Rounds 60-63 (full rounds)
    {{0x78d04aa6f8747ad0ULL, 0x5da18ea9d8e4f101ULL, 0x626ed93491bda32eULL, 0x1acd63c67fbc9ab1ULL},
     {0xca8c86cd2a28b5a5ULL, 0x1bf93375e2323ec3ULL, 0xc4e3144be58ef690ULL, 0x19f8a5d670e8ab66ULL},
     {0x8c49833d53bb8085ULL, 0x8181585d2572d76fULL, 0xb97091f1e35c59e3ULL, 0x1c0dc443519ad7a8ULL}},
    {{0xc4180e4c3224987dULL, 0x01f021afb1e35e28ULL, 0x190e421dc19fbeabULL, 0x14b39e7aa4068dbeULL},
     {0x0909ccf1595b43f2ULL, 0xfbcbcc80214f26a3ULL, 0x74ca654992defe7fULL, 0x1d449b71bd826ec5ULL},
     {0x89de141689d12527ULL, 0xf91f9a46a0e9c058ULL, 0x60fe9d8e134d5cefULL, 0x1ea2c9a89baaddbbULL}},
    {{0x0ec5c4f9e8b7ad7bULL, 0xf8617361c3ba7c52ULL, 0x994427cc86296242ULL, 0x0478d66d43535a8cULL},
     {0x6091ccf1595b43f2ULL, 0xdd866a87ef75039bULL, 0x87a96d1381e846afULL, 0x19272db71eece6a6ULL},
     {0x994427cc86296242ULL, 0x60b145f8617361c3ULL, 0xe6f608f3b2717f9cULL, 0x14226537335cab33ULL}},
    {{0x4f847f760054f4a3ULL, 0x134334da98ea033ULL, 0xcb1929a82650f328ULL, 0x01fd6af15956294fULL},
     {0xa15d3f74ca654992ULL, 0xbfcbcc80214f26a3ULL, 0x043bfc303b6f7c86ULL, 0x18e5abedd626ec30ULL},
     {0x2e660b145994427cULL, 0xef8617361c3ba7c5ULL, 0x2eef542b12ed2519ULL, 0x0fc1bbceba0590f5ULL}}
};

/* ============================================================================
 * Poseidon2 Implementation (copied from runner_fuzz.c)
 * ============================================================================ */

static void add_round_constant(poseidon_state_3 *state, int round, const field_params *p) {
    bn254_fe rc;
    for (int i = 0; i < 3; i++) {
        bn254_from_limbs(&rc, RC_3[round][i]);
        bn254_to_mont(&rc, &rc, p);
        bn254_add(&state->elem[i], &state->elem[i], &rc, p);
    }
}

static void sbox5(bn254_fe *out, const bn254_fe *x, const field_params *p) {
    bn254_fe x2, x4;
    bn254_mul(&x2, x, x, p);
    bn254_mul(&x4, &x2, &x2, p);
    bn254_mul(out, x, &x4, p);
}

static void sbox_full(poseidon_state_3 *state, const field_params *p) {
    for (int i = 0; i < 3; i++) {
        sbox5(&state->elem[i], &state->elem[i], p);
    }
}

static void sbox_partial(poseidon_state_3 *state, const field_params *p) {
    sbox5(&state->elem[0], &state->elem[0], p);
}

static void mds_external(poseidon_state_3 *state, const field_params *p) {
    bn254_fe sum, temp;
    bn254_zero(&sum);
    bn254_add(&sum, &state->elem[0], &state->elem[1], p);
    bn254_add(&sum, &sum, &state->elem[2], p);
    for (int i = 0; i < 3; i++) {
        bn254_copy(&temp, &state->elem[i]);
        bn254_add(&state->elem[i], &temp, &sum, p);
    }
}

static void mds_internal(poseidon_state_3 *state, const field_params *p) {
    bn254_fe sum, s2_doubled;
    bn254_zero(&sum);
    bn254_add(&sum, &state->elem[0], &state->elem[1], p);
    bn254_add(&sum, &sum, &state->elem[2], p);
    bn254_add(&s2_doubled, &state->elem[2], &state->elem[2], p);
    bn254_add(&state->elem[0], &state->elem[0], &sum, p);
    bn254_add(&state->elem[1], &state->elem[1], &sum, p);
    bn254_add(&state->elem[2], &s2_doubled, &sum, p);
}

static void full_round(poseidon_state_3 *state, int round, const field_params *p) {
    add_round_constant(state, round, p);
    sbox_full(state, p);
    mds_external(state, p);
}

static void partial_round(poseidon_state_3 *state, int round, const field_params *p) {
    add_round_constant(state, round, p);
    sbox_partial(state, p);
    mds_internal(state, p);
}

static void poseidon2_permutation(poseidon_state_3 *state, const field_params *p) {
    mds_external(state, p);
    for (int r = 0; r < 4; r++) full_round(state, r, p);
    for (int r = 4; r < 60; r++) partial_round(state, r, p);
    for (int r = 60; r < 64; r++) full_round(state, r, p);
}

/* ============================================================================
 * Hash Functions
 * ============================================================================ */

/* XOR-based hash (testHash from Merkle.lean) - NOT cryptographic! */
static inline uint64_t xor_hash(uint64_t a, uint64_t b) {
    return (a ^ b) + GOLDEN_RATIO;
}

/* Poseidon2 2-to-1 hash for Merkle trees */
static void poseidon2_merkle_hash(bn254_fe *out,
                                   const bn254_fe *left,
                                   const bn254_fe *right,
                                   const field_params *p) {
    poseidon_state_3 state;

    // Initialize state = [left, right, 0]
    bn254_copy(&state.elem[0], left);
    bn254_copy(&state.elem[1], right);
    bn254_zero(&state.elem[2]);

    // Apply permutation
    poseidon2_permutation(&state, p);

    // Squeeze: return first element
    bn254_copy(out, &state.elem[0]);
}

/* ============================================================================
 * Get current time in nanoseconds
 * ============================================================================ */

static uint64_t get_time_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
}

/* ============================================================================
 * Merkle Tree Builders
 * ============================================================================ */

/* Build Merkle tree with XOR hash (simplified: single uint64 per node) */
static uint64_t build_merkle_xor(const uint64_t *leaves, int n) {
    if (n <= 0) return 0;
    if (n == 1) return leaves[0];

    uint64_t *buffer = malloc((size_t)n * 2 * sizeof(uint64_t));
    memcpy(buffer, leaves, (size_t)n * sizeof(uint64_t));

    int current_size = n;
    int read_offset = 0;
    int write_offset = n;

    while (current_size > 1) {
        int next_size = current_size / 2;
        for (int i = 0; i < next_size; i++) {
            buffer[write_offset + i] = xor_hash(
                buffer[read_offset + 2*i],
                buffer[read_offset + 2*i + 1]
            );
        }
        read_offset = write_offset;
        write_offset += next_size;
        current_size = next_size;
    }

    uint64_t root = buffer[read_offset];
    free(buffer);
    return root;
}

/* Build Merkle tree with Poseidon2 hash */
static void build_merkle_poseidon(bn254_fe *root,
                                   const bn254_fe *leaves,
                                   int n,
                                   const field_params *p) {
    if (n <= 0) return;
    if (n == 1) {
        bn254_copy(root, &leaves[0]);
        return;
    }

    bn254_fe *buffer = malloc((size_t)n * 2 * sizeof(bn254_fe));
    memcpy(buffer, leaves, (size_t)n * sizeof(bn254_fe));

    int current_size = n;
    int read_offset = 0;
    int write_offset = n;

    while (current_size > 1) {
        int next_size = current_size / 2;
        for (int i = 0; i < next_size; i++) {
            poseidon2_merkle_hash(
                &buffer[write_offset + i],
                &buffer[read_offset + 2*i],
                &buffer[read_offset + 2*i + 1],
                p
            );
        }
        read_offset = write_offset;
        write_offset += next_size;
        current_size = next_size;
    }

    bn254_copy(root, &buffer[read_offset]);
    free(buffer);
}

/* ============================================================================
 * Benchmarks
 * ============================================================================ */

static void benchmark_single_hash(const field_params *p) {
    printf("═══════════════════════════════════════════════════════════════\n");
    printf("  TEST 3A: SINGLE HASH BENCHMARK\n");
    printf("═══════════════════════════════════════════════════════════════\n\n");

    const int iterations = 100000;

    // XOR hash benchmark
    uint64_t xor_start = get_time_ns();
    uint64_t xor_accum = 0;
    for (int i = 0; i < iterations; i++) {
        xor_accum = xor_hash(xor_accum + (uint64_t)i, (uint64_t)i + 1);
    }
    uint64_t xor_end = get_time_ns();
    uint64_t xor_total = xor_end - xor_start;
    double xor_per_hash = (double)xor_total / iterations;

    printf("  XOR Hash (NOT cryptographic!):\n");
    printf("    Per hash:      %.1f ns\n", xor_per_hash);
    printf("    Throughput:    %.0f hashes/sec\n\n", 1e9 / xor_per_hash);

    // Poseidon2 hash benchmark
    bn254_fe left, right, result;
    bn254_from_u64(&left, 0, p);
    bn254_from_u64(&right, 0, p);

    uint64_t pos_start = get_time_ns();
    for (int i = 0; i < iterations; i++) {
        bn254_copy(&left, &result);
        bn254_from_u64(&right, (uint64_t)i, p);
        poseidon2_merkle_hash(&result, &left, &right, p);
    }
    uint64_t pos_end = get_time_ns();
    uint64_t pos_total = pos_end - pos_start;
    double pos_per_hash = (double)pos_total / iterations;

    printf("  Poseidon2 BN254 (cryptographic):\n");
    printf("    Per hash:      %.1f ns\n", pos_per_hash);
    printf("    Throughput:    %.0f hashes/sec\n\n", 1e9 / pos_per_hash);

    double slowdown = pos_per_hash / xor_per_hash;
    printf("  ┌────────────────────────────────────┐\n");
    printf("  │ SLOWDOWN FACTOR: %.0fx             │\n", slowdown);
    printf("  └────────────────────────────────────┘\n\n");
}

static void benchmark_merkle_tree(const field_params *p) {
    printf("═══════════════════════════════════════════════════════════════\n");
    printf("  TEST 3B: MERKLE TREE BENCHMARK (XOR vs Poseidon2)\n");
    printf("═══════════════════════════════════════════════════════════════\n\n");

    int tree_sizes[] = {8, 64, 256, 1024, 4096, 16384};
    int num_sizes = (int)(sizeof(tree_sizes) / sizeof(tree_sizes[0]));

    printf("  Tree Size | XOR (µs)  | Poseidon2 (µs) | Slowdown | Hashes\n");
    printf("  ----------|-----------|----------------|----------|--------\n");

    for (int s = 0; s < num_sizes; s++) {
        int n = tree_sizes[s];
        int hash_ops = n - 1;

        // Create leaves
        uint64_t *xor_leaves = malloc((size_t)n * sizeof(uint64_t));
        bn254_fe *pos_leaves = malloc((size_t)n * sizeof(bn254_fe));

        for (int i = 0; i < n; i++) {
            xor_leaves[i] = (uint64_t)i + 1;
            bn254_from_u64(&pos_leaves[i], (uint64_t)i + 1, p);
        }

        // XOR benchmark
        int xor_iterations = (n <= 1024) ? 10000 : 1000;
        uint64_t xor_start = get_time_ns();
        for (int iter = 0; iter < xor_iterations; iter++) {
            build_merkle_xor(xor_leaves, n);
        }
        uint64_t xor_end = get_time_ns();
        double xor_us = (double)(xor_end - xor_start) / xor_iterations / 1000.0;

        // Poseidon2 benchmark
        int pos_iterations = (n <= 64) ? 1000 : (n <= 256) ? 100 : (n <= 1024) ? 10 : 1;
        bn254_fe pos_root;
        uint64_t pos_start = get_time_ns();
        for (int iter = 0; iter < pos_iterations; iter++) {
            build_merkle_poseidon(&pos_root, pos_leaves, n, p);
        }
        uint64_t pos_end = get_time_ns();
        double pos_us = (double)(pos_end - pos_start) / pos_iterations / 1000.0;

        double slowdown = pos_us / xor_us;

        printf("  %7d   | %9.2f | %14.2f | %8.0fx | %6d\n",
               n, xor_us, pos_us, slowdown, hash_ops);

        free(xor_leaves);
        free(pos_leaves);
    }

    printf("\n");
}

static void print_analysis(void) {
    printf("═══════════════════════════════════════════════════════════════\n");
    printf("  ANALYSIS & VERDICT\n");
    printf("═══════════════════════════════════════════════════════════════\n\n");

    printf("  Expected Slowdown Thresholds:\n");
    printf("    < 1000x:    Excellent (optimized implementation)\n");
    printf("    1000-3000x: Good (typical for production)\n");
    printf("    3000-5000x: Acceptable (may optimize later)\n");
    printf("    > 5000x:    INVESTIGATE - possible adapter issue\n\n");

    printf("  Security Notes:\n");
    printf("    - XOR hash provides NO cryptographic security\n");
    printf("    - Poseidon2 provides ~128-bit security\n");
    printf("    - The slowdown is the cost of real security\n\n");
}

/* ============================================================================
 * Main
 * ============================================================================ */

int main(void) {
    printf("\n");
    printf("╔═══════════════════════════════════════════════════════════════╗\n");
    printf("║   STEP 5.1: POSEIDON2 INTEGRATION PERFORMANCE TAX ANALYSIS    ║\n");
    printf("╚═══════════════════════════════════════════════════════════════╝\n\n");

    // Initialize field parameters
    field_params params;
    bn254_init_params(&params);

    // Run benchmarks
    benchmark_single_hash(&params);
    benchmark_merkle_tree(&params);
    print_analysis();

    return 0;
}
