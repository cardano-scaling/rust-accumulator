#ifndef BEND_ACCUMULATOR_H
#define BEND_ACCUMULATOR_H
#include <stddef.h>
#include <stdint.h>

enum bend_status { BEND_OK, BEND_REJECTED, BEND_BAD_ARGUMENT, BEND_INTERNAL };

/* Experimental CPU adapter, pinned to Bend 2.0.37. Scalars are canonical,
 * 32-byte little-endian integers, NOT blst's Montgomery representation.
 * count <= 256; output_count must be count + 1. Output is untouched on errors.
 * Inputs/output may overlap. Calls entering Bend are serialized; empty and
 * singleton results bypass the runtime. The runtime persists until process exit.
 * The adapter preserves the host's signal handlers and alternate signal stack.
 * This interface does not promise constant-time execution. */
int bend_coefficients(const uint8_t *inputs, size_t count, size_t basis_size,
                      uint8_t *output, size_t output_count);

/* Diagnostic arithmetic entry point: operation 1=add, 2=subtract, 3=multiply. */
int bend_scalar(unsigned operation, const uint8_t left[32],
                const uint8_t right[32], uint8_t output[32]);
#endif
