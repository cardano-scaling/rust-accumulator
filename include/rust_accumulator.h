#include "blst.h"
#include <stddef.h>

// Define the Scalar structure as it is in Rust
typedef struct {
  blst_fr inner;
} Scalar;

// Define the G1Projective structure as it is in Rust
typedef struct {
  blst_p1 inner;
} G1Projective;

// Define the G2Projective structure as it is in Rust
typedef struct {
  blst_p2 inner;
} G2Projective;

void get_poly_commitment_g1(G1Projective *return_point, Scalar *scalars_ptr, size_t scalars_len, G1Projective *points_ptr, size_t points_len);

void get_poly_commitment_g2(G2Projective *return_point, Scalar *scalars_ptr, size_t scalars_len, G2Projective *points_ptr, size_t points_len);

