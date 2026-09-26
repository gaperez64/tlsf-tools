#ifndef TLSF_SHA256_H
#define TLSF_SHA256_H

#include <stddef.h>

void sha256_hex(const void *bytes, size_t length, char output[65]);

#endif
