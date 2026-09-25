#include "sha256.h"

#include <stdint.h>
#include <string.h>

static const uint32_t round_constants[64] = {
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1,
    0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
    0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786,
    0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147,
    0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
    0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a,
    0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
    0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2};

static uint32_t rotate_right(uint32_t value, unsigned amount) {
  return (value >> amount) | (value << (32u - amount));
}

static void process_block(uint32_t state[8], const uint8_t block[64]) {
  uint32_t words[64];
  for (unsigned i = 0; i < 16; i++)
    words[i] = ((uint32_t)block[4 * i] << 24) |
               ((uint32_t)block[4 * i + 1] << 16) |
               ((uint32_t)block[4 * i + 2] << 8) | block[4 * i + 3];
  for (unsigned i = 16; i < 64; i++) {
    uint32_t s0 = rotate_right(words[i - 15], 7) ^
                  rotate_right(words[i - 15], 18) ^ (words[i - 15] >> 3);
    uint32_t s1 = rotate_right(words[i - 2], 17) ^
                  rotate_right(words[i - 2], 19) ^ (words[i - 2] >> 10);
    words[i] = words[i - 16] + s0 + words[i - 7] + s1;
  }
  uint32_t a = state[0], b = state[1], c = state[2], d = state[3];
  uint32_t e = state[4], f = state[5], g = state[6], h = state[7];
  for (unsigned i = 0; i < 64; i++) {
    uint32_t s1 =
        rotate_right(e, 6) ^ rotate_right(e, 11) ^ rotate_right(e, 25);
    uint32_t choice = (e & f) ^ (~e & g);
    uint32_t t1 = h + s1 + choice + round_constants[i] + words[i];
    uint32_t s0 =
        rotate_right(a, 2) ^ rotate_right(a, 13) ^ rotate_right(a, 22);
    uint32_t majority = (a & b) ^ (a & c) ^ (b & c);
    uint32_t t2 = s0 + majority;
    h = g;
    g = f;
    f = e;
    e = d + t1;
    d = c;
    c = b;
    b = a;
    a = t1 + t2;
  }
  state[0] += a;
  state[1] += b;
  state[2] += c;
  state[3] += d;
  state[4] += e;
  state[5] += f;
  state[6] += g;
  state[7] += h;
}

void sha256_hex(const void *bytes, size_t length, char output[65]) {
  static const char alphabet[] = "0123456789abcdef";
  uint32_t state[8] = {0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
                       0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19};
  const uint8_t *input = bytes;
  size_t complete = length / 64;
  for (size_t i = 0; i < complete; i++)
    process_block(state, input + 64 * i);
  uint8_t tail[128] = {0};
  size_t remaining = length % 64;
  memcpy(tail, input + 64 * complete, remaining);
  tail[remaining] = 0x80;
  size_t padded = remaining < 56 ? 64 : 128;
  uint64_t bits = (uint64_t)length * 8;
  for (unsigned i = 0; i < 8; i++)
    tail[padded - 1 - i] = (uint8_t)(bits >> (8 * i));
  process_block(state, tail);
  if (padded == 128)
    process_block(state, tail + 64);
  for (unsigned i = 0; i < 8; i++)
    for (unsigned j = 0; j < 4; j++) {
      uint8_t octet = (uint8_t)(state[i] >> (24 - 8 * j));
      output[8 * i + 2 * j] = alphabet[octet >> 4];
      output[8 * i + 2 * j + 1] = alphabet[octet & 15];
    }
  output[64] = '\0';
}
