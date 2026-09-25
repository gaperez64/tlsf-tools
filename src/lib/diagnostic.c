#include "diagnostic.h"

static _Thread_local FILE *current_stream;

FILE *tlsf_diagnostic_stream(void) {
  return current_stream ? current_stream : stderr;
}

FILE *tlsf_diagnostic_swap(FILE *stream) {
  FILE *previous = current_stream;
  current_stream = stream;
  return previous;
}
