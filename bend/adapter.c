/* This deliberately small adapter uses the pinned compiler's internal ABI.
 * Generated code and this file are compiled as a single translation unit.
 * The raw Rust/blst interface remains unchanged; conversions happen explicitly.
 */
#define main bend_generated_main
#include "bend_generated.c"
#undef main
#include "adapter.h"

#define BEND_API __attribute__((visibility("default")))
static pthread_once_t bend_once = PTHREAD_ONCE_INIT;
static pthread_mutex_t bend_lock = PTHREAD_MUTEX_INITIALIZER;

static void bend_initialize(void) {
  corpus_setup(false, 1, 0);
  /* Match this compiler release's evaluation stack and guard, without
   * pool_stack's process-wide signal handlers or caller-thread alt stack.
   * A library must preserve the host's fault handling. */
  const size_t stack_size = (size_t)1 << 31;
  char *stack = pool_mmap(stack_size + 16384);
  if (mprotect(stack + stack_size, 16384, PROT_NONE) != 0)
    err_fail("stack guard failed");
  io_stk = (Term *)stack;
}

static Term bend_pair(Env e, unsigned constructor, Term a, Term b) {
  u64 node = heap_alloc(e, cls_fit(2));
  e.mem[node] = rfc_seal(e, a);
  e.mem[node + 1] = rfc_seal(e, b);
  return term_ctr(constructor, node);
}

static uint32_t bend_load_limb(const uint8_t *bytes) {
  return (uint32_t)bytes[0] | (uint32_t)bytes[1] << 8 |
         (uint32_t)bytes[2] << 16 | (uint32_t)bytes[3] << 24;
}

static Term bend_field(Env e, const uint8_t bytes[32]) {
  u64 node = heap_alloc(e, cls_fit(8));
  for (unsigned limb = 0; limb < 8; ++limb)
    e.mem[node + limb] = bend_load_limb(bytes + 4 * limb);
  return term_ctr(CID_SCALAR_FR, node);
}

static bool bend_read_field(Env e, Term field, uint8_t bytes[32]) {
  if (term_tag(field) != TAG_CTR || term_aux(field) != CID_SCALAR_FR) return false;
  u64 at = term_peek(e.mem, field);
  for (unsigned limb = 0; limb < 8; ++limb) {
    if (e.mem[at + limb] > UINT32_MAX) return false;
    for (unsigned byte = 0; byte < 4; ++byte)
      bytes[4 * limb + byte] = (uint8_t)(e.mem[at + limb] >> (8 * byte));
  }
  return true;
}

static bool bend_canonical(const uint8_t x[32]) {
  static const uint8_t modulus[32] = {
    1, 0, 0, 0, 255, 255, 255, 255, 254, 91, 254, 255, 2, 164, 189, 83,
    5, 216, 161, 9, 8, 216, 57, 51, 72, 125, 157, 41, 83, 167, 237, 115
  };
  for (unsigned i = 32; i-- > 0;)
    if (x[i] != modulus[i]) return x[i] < modulus[i];
  return false;
}

/* dispatch's flattened Request: tag plus two eight-limb Scalars.
 * Its Maybe result has two words. The public byte encoding is unchanged. */
static int bend_evaluate(Env e, const Term arguments[17],
                         uint8_t *output, size_t count) {
  if (fid_arity(FID_DISPATCH) != 17 || fid_resw(FID_DISPATCH) != 0)
    return BEND_INTERNAL;
  u64 call = task_node(e, FID_DISPATCH, TERM_HOLE, 0, 0);
  memcpy(e.mem + call, arguments, 17 * sizeof(Term));
  Term accepted = corpus_eval(e.mem, term_tsk(FID_DISPATCH, call));
  if (accepted == 0) return BEND_REJECTED;
  if (accepted != 1) return BEND_INTERNAL;
  Term result = e.mem[H_ROOT_WORD + 1];
  Term list = result;
  uint8_t temporary[257 * 32];
  int status = BEND_OK;
  for (size_t i = 0; i < count; ++i) {
    if (term_tag(list) != TAG_CTR || term_aux(list) != CID_CON) {
      status = BEND_INTERNAL;
      break;
    }
    u64 at = term_peek(e.mem, list);
    if (!bend_read_field(e, e.mem[at], temporary + 32 * i)) {
      status = BEND_INTERNAL;
      break;
    }
    list = e.mem[at + 1];
  }
  if (status == BEND_OK && (term_tag(list) != TAG_PAK || term_aux(list) != CID_NIL))
    status = BEND_INTERNAL;
  term_drop(e, result);
  if (status == BEND_OK) memcpy(output, temporary, count * 32);
  return status;
}

BEND_API int bend_coefficients(const uint8_t *inputs, size_t count,
                               size_t basis_size, uint8_t *output,
                               size_t output_count) {
  if (count > 256 || output_count != count + 1 || output == NULL ||
      (count != 0 && inputs == NULL) || basis_size > 257) return BEND_BAD_ARGUMENT;
  if (basis_size != count + 1) return BEND_REJECTED;
  /* The empty/singleton laws give [1] and [input, 1]. These byte copies need
   * no field arithmetic or runtime. Validate before touching aliased output. */
  if (count <= 1) {
    if (count == 1) {
      if (!bend_canonical(inputs)) return BEND_REJECTED;
      memmove(output, inputs, 32);
    }
    memset(output + 32 * count, 0, 32);
    output[32 * count] = 1;
    return BEND_OK;
  }
  pthread_once(&bend_once, bend_initialize);
  pthread_mutex_lock(&bend_lock);
  Env e = { CORPUS, ALC[0] };
  Term list = term_pak(CID_NIL, 0);
  for (size_t i = count; i-- > 0;)
    list = bend_pair(e, CID_CON, bend_field(e, inputs + 32 * i), list);
  Term arguments[17] = {0, list, basis_size};
  int status = bend_evaluate(e, arguments, output, output_count);
  pthread_mutex_unlock(&bend_lock);
  return status;
}

BEND_API int bend_scalar(unsigned operation, const uint8_t left[32],
                         const uint8_t right[32], uint8_t output[32]) {
  if (operation < 1 || operation > 3 || !left || !right || !output)
    return BEND_BAD_ARGUMENT;
  if (!bend_canonical(left) || !bend_canonical(right)) return BEND_REJECTED;
  pthread_once(&bend_once, bend_initialize);
  pthread_mutex_lock(&bend_lock);
  Env e = { CORPUS, ALC[0] };
  Term arguments[17] = {operation};
  for (unsigned limb = 0; limb < 8; ++limb) {
    arguments[1 + limb] = bend_load_limb(left + 4 * limb);
    arguments[9 + limb] = bend_load_limb(right + 4 * limb);
  }
  int status = bend_evaluate(e, arguments, output, 1);
  pthread_mutex_unlock(&bend_lock);
  return status;
}
