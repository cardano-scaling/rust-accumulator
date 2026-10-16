#!/usr/bin/env python3
"""Exercise the generated C and byte adapter under Address/UndefinedBehaviorSanitizer."""
import argparse
import os
from pathlib import Path
import random
import subprocess
import tempfile

from test import MODULUS, ROOT, encoded, oracle


HARNESS = r'''
#define _GNU_SOURCE
#include "adapter.h"
#include <assert.h>
#include <pthread.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <signal.h>

typedef struct { size_t count; const uint8_t *input, *expected; } Case;
#include "fixtures.h"

static void exercise(const Case *c) {
  size_t in_size = 32 * c->count, out_size = in_size + 32;
  uint8_t *in = malloc(in_size ? in_size : 1), *out = malloc(out_size);
  assert(in && out);
  memcpy(in, c->input, in_size);
  memset(out, 0xa5, out_size);
  assert(bend_coefficients(in, c->count, c->count, out, c->count + 1) == BEND_REJECTED);
  for (size_t i = 0; i < out_size; ++i) assert(out[i] == 0xa5);
  assert(bend_coefficients(in, c->count, c->count + 1, out, c->count + 1) == BEND_OK);
  assert(memcmp(out, c->expected, out_size) == 0);
  free(in);
  free(out);
  for (unsigned mode = 0; mode < 3; ++mode) {
    uint8_t *memory = malloc(out_size + 7);
    assert(memory);
    in = memory + (mode == 2 ? 7 : 0);
    out = memory + (mode == 1 ? 7 : 0);
    memcpy(in, c->input, in_size);
    assert(bend_coefficients(in, c->count, c->count + 1, out, c->count + 1) == BEND_OK);
    assert(memcmp(out, c->expected, out_size) == 0);
    free(memory);
  }
}

static void *worker(void *unused) {
  (void)unused;
  for (unsigned round = 0; round < 3; ++round)
    for (size_t i = 0; i < sizeof(cases)/sizeof(cases[0]); ++i) exercise(&cases[i]);
  return NULL;
}

static void host_handler(int signal) { (void)signal; abort(); }

int main(void) {
  struct sigaction host = { .sa_handler = host_handler }, old_segv, old_bus, current;
  sigemptyset(&host.sa_mask);
  assert(sigaction(SIGSEGV, &host, &old_segv) == 0);
  assert(sigaction(SIGBUS, &host, &old_bus) == 0);
  stack_t previous_stack, current_stack;
  stack_t host_stack = { .ss_sp = malloc(SIGSTKSZ), .ss_size = SIGSTKSZ, .ss_flags = 0 };
  assert(host_stack.ss_sp && sigaltstack(&host_stack, &previous_stack) == 0);
  uint8_t output[257*32], invalid[257*32];
  memset(output, 0xa5, sizeof(output));
  memset(invalid, 0xff, sizeof(invalid));
  assert(bend_coefficients(NULL, 1, 2, output, 2) == BEND_BAD_ARGUMENT);
  assert(bend_coefficients(NULL, 0, 1, NULL, 1) == BEND_BAD_ARGUMENT);
  assert(bend_coefficients(NULL, 257, 258, output, 258) == BEND_BAD_ARGUMENT);
  assert(bend_coefficients(NULL, 0, 1, output, 0) == BEND_BAD_ARGUMENT);
  for (size_t n = 1; n <= 256; ++n) {
    assert(bend_coefficients(invalid, n, n + 1, output, n + 1) == BEND_REJECTED);
    assert(bend_coefficients(invalid, n, n + 1, invalid, n + 1) == BEND_REJECTED);
  }
  for (size_t i = 0; i < sizeof(output); ++i) assert(output[i] == 0xa5);
  for (size_t i = 0; i < sizeof(invalid); ++i) assert(invalid[i] == 0xff);
  assert(bend_coefficients(NULL, 0, 1, output, 1) == BEND_OK);
  assert(output[0] == 1);
  for (size_t i = 1; i < 32; ++i) assert(output[i] == 0);
  pthread_t threads[4];
  for (unsigned i = 0; i < 4; ++i) assert(pthread_create(&threads[i], NULL, worker, NULL) == 0);
  for (unsigned i = 0; i < 4; ++i) assert(pthread_join(threads[i], NULL) == 0);
  assert(sigaction(SIGSEGV, NULL, &current) == 0 && current.sa_handler == host_handler);
  assert(sigaction(SIGBUS, NULL, &current) == 0 && current.sa_handler == host_handler);
  assert(sigaltstack(NULL, &current_stack) == 0);
  assert(current_stack.ss_sp == host_stack.ss_sp && current_stack.ss_size == host_stack.ss_size);
  assert(current_stack.ss_flags == 0);
  assert(sigaction(SIGSEGV, &old_segv, NULL) == 0);
  assert(sigaction(SIGBUS, &old_bus, NULL) == 0);
  assert(sigaltstack(&previous_stack, NULL) == 0);
  free(host_stack.ss_sp);
  puts("PASS: ASan/UBSan boundary, aliasing, rejection, concurrency and host-signal checks");
  return 0;
}
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", type=Path, default=ROOT / "target/karatsuba",
                        help="directory containing bend_generated.c from build.py")
    args = parser.parse_args()
    if not (args.build / "bend_generated.c").is_file():
        parser.error("run build.py first")
    rng = random.Random(0xacc)
    cases = [[], [0], [1], [MODULUS-1]]
    for n in [2, 3, 4, 8, 16, 31, 32, 33, 63, 64, 65, 96, 127, 128, 129, 192, 255, 256]:
        cases.extend([[rng.randrange(MODULUS) for _ in range(n)], [0]*n,
                      [1 if i % 2 else MODULUS-1 for i in range(n)]])
    declarations = []
    for i, xs in enumerate(cases):
        for label, values in [("input", xs), ("expected", oracle(xs))]:
            data = b"".join(map(encoded, values)) or b"\0"
            declarations.append(f"static const uint8_t {label}_{i}[] = {{" +
                                ",".join(map(str, data)) + "};")
    declarations.append("static const Case cases[] = {" + ",".join(
        f"{{{len(xs)}, input_{i}, expected_{i}}}" for i, xs in enumerate(cases)) + "};")
    with tempfile.TemporaryDirectory(prefix="bend-sanitizers-") as temporary:
        directory = Path(temporary)
        (directory / "fixtures.h").write_text("\n".join(declarations) + "\n")
        (directory / "harness.c").write_text(HARNESS)
        subprocess.run(["clang", "-std=c11", "-O1", "-g", "-pthread",
            "-fsanitize=address,undefined", "-fno-sanitize-recover=all", "-fno-omit-frame-pointer",
            "-I", str(args.build.resolve()), "-I", str(ROOT), str(ROOT / "adapter.c"),
            str(directory / "harness.c"), "-lm", "-o", str(directory / "check")], check=True)
        subprocess.run([str(directory / "check")], check=True, env={**os.environ,
            "ASAN_OPTIONS": "detect_leaks=1:abort_on_error=1", "UBSAN_OPTIONS": "halt_on_error=1"})


if __name__ == "__main__":
    main()
