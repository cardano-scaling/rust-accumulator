# BLS12-381 scalars in eight little-endian machine limbs.
# Public values are canonical integers, not Montgomery residues.
# All arithmetic remains pure Bend; U32 operations compile to machine words.
import Base

type Scalar is Data:
  Fr{a: U32, b: U32, c: U32, d: U32, e: U32, f: U32, g: U32, h: U32}

def modulus() -> Scalar:
  Fr{1, 4294967295, 4294859774, 1404937218,
     161601541, 859428872, 698187080, 1944954707}

def zero() -> Scalar:
  Fr{0, 0, 0, 0, 0, 0, 0, 0}

def one() -> Scalar:
  Fr{1, 0, 0, 0, 0, 0, 0, 0}

def flag(b: Bool) -> U32:
  match b:
    case False{}:
      0
    case True{}:
      1

type Carry is Data:
  Carry{word: U32, carry: U32}

def word(r: Carry) -> U32:
  match r:
    case Carry{w, c}:
      w

def carry(r: Carry) -> U32:
  match r:
    case Carry{w, c}:
      c

type Raw is Data:
  Raw{value: Scalar, carry: U32}

def value(r: Raw) -> Scalar:
  match r:
    case Raw{v, c}:
      v

def borrowed(r: Raw) -> Bool:
  match r:
    case Raw{v, c}:
      U32.is_eq(c, 1)

def adc(+a: U32, b: U32, carry: U32) -> Carry:
  +s = U32.add(a, b)
  +t = U32.add(s, carry)
  Carry{t, U32.or(flag(U32.is_lt(s, a)), flag(U32.is_lt(t, s)))}

def sbb(+a: U32, +b: U32, +borrow: U32) -> Carry:
  +s = U32.sub(a, b)
  Carry{U32.sub(s, borrow), U32.or(flag(U32.is_lt(a, b)), flag(U32.is_lt(s, borrow)))}

def add_raw(x: Scalar, y: Scalar) -> Raw:
  match x y:
    case Fr{xa, xb, xc, xd, xe, xf, xg, xh} Fr{ya, yb, yc, yd, ye, yf, yg, yh}:
      +r1 = adc(xa, ya, 0)
      +r2 = adc(xb, yb, carry(r1))
      +r3 = adc(xc, yc, carry(r2))
      +r4 = adc(xd, yd, carry(r3))
      +r5 = adc(xe, ye, carry(r4))
      +r6 = adc(xf, yf, carry(r5))
      +r7 = adc(xg, yg, carry(r6))
      +r8 = adc(xh, yh, carry(r7))
      Raw{Fr{word(r1), word(r2), word(r3), word(r4), word(r5), word(r6), word(r7), word(r8)}, carry(r8)}

def sub_raw(x: Scalar, y: Scalar) -> Raw:
  match x y:
    case Fr{xa, xb, xc, xd, xe, xf, xg, xh} Fr{ya, yb, yc, yd, ye, yf, yg, yh}:
      +r1 = sbb(xa, ya, 0)
      +r2 = sbb(xb, yb, carry(r1))
      +r3 = sbb(xc, yc, carry(r2))
      +r4 = sbb(xd, yd, carry(r3))
      +r5 = sbb(xe, ye, carry(r4))
      +r6 = sbb(xf, yf, carry(r5))
      +r7 = sbb(xg, yg, carry(r6))
      +r8 = sbb(xh, yh, carry(r7))
      Raw{Fr{word(r1), word(r2), word(r3), word(r4), word(r5), word(r6), word(r7), word(r8)}, carry(r8)}

def valid(a: Scalar) -> Bool:
  borrowed(sub_raw(a, modulus()))

def select(a: Scalar, b: Scalar, use_a: Bool) -> Scalar:
  match use_a:
    case True{}:
      a
    case False{}:
      b

# Canonical operands have a+b < 2p < 2^256; one subtraction suffices.
def reduce(+a: Scalar) -> Scalar:
  +r = sub_raw(a, modulus())
  select(a, value(r), borrowed(r))

def add(a: Scalar, b: Scalar) -> Scalar:
  reduce(value(add_raw(a, b)))

def sub(a: Scalar, b: Scalar) -> Scalar:
  +r = sub_raw(a, b)
  select(value(add_raw(value(r), modulus())), value(r), borrowed(r))

# Twelve radix-2^23 digits replace seventeen radix-2^15 digits.
# Nat arithmetic lowers to native words, with a checked 48-bit limit.
# Two 23-bit products, a digit and the carry remain below that limit.
type Digits is Data:
  D{d0: U32, d1: U32, d2: U32, d3: U32, d4: U32, d5: U32, d6: U32, d7: U32, d8: U32, d9: U32, d10: U32, d11: U32}

def low(n: Nat) -> U32:
  U32.from_nat(Nat.mod(n, 8388608n))

def high(n: Nat) -> Nat:
  Nat.div(n, 8388608n)

def digit(n: U32) -> Nat:
  U32.to_nat(U32.and(n, 8388607))

def product(a: U32, b: U32) -> Nat:
  Nat.mul(digit(a), digit(b))

def digits(x: Scalar) -> Digits:
  match x:
    case Fr{+a, +b, +c, +d, +e, +f, +g, +h}:
      D{U32.and(a, 8388607),
        U32.and(U32.or(U32.shrn(a, 23n), U32.shln(b, 9n)), 8388607),
        U32.and(U32.or(U32.shrn(b, 14n), U32.shln(c, 18n)), 8388607),
        U32.and(U32.shrn(c, 5n), 8388607),
        U32.and(U32.or(U32.shrn(c, 28n), U32.shln(d, 4n)), 8388607),
        U32.and(U32.or(U32.shrn(d, 19n), U32.shln(e, 13n)), 8388607),
        U32.and(U32.or(U32.shrn(e, 10n), U32.shln(f, 22n)), 8388607),
        U32.and(U32.shrn(f, 1n), 8388607),
        U32.and(U32.or(U32.shrn(f, 24n), U32.shln(g, 8n)), 8388607),
        U32.and(U32.or(U32.shrn(g, 15n), U32.shln(h, 17n)), 8388607),
        U32.and(U32.shrn(h, 6n), 8388607),
        U32.shrn(h, 29n)}

# Preserve bit 255: the unreduced result may be above p, but is below 2p.
def from_digits(x: Digits) -> Scalar:
  match x:
    case D{+d0, +d1, +d2, +d3, +d4, +d5, +d6, +d7, +d8, +d9, +d10, +d11}:
      Fr{U32.or(d0, U32.shln(d1, 23n)),
         U32.or(U32.shrn(d1, 9n), U32.shln(d2, 14n)),
         U32.or(U32.or(U32.shrn(d2, 18n), U32.shln(d3, 5n)), U32.shln(d4, 28n)),
         U32.or(U32.shrn(d4, 4n), U32.shln(d5, 19n)),
         U32.or(U32.shrn(d5, 13n), U32.shln(d6, 10n)),
         U32.or(U32.or(U32.shrn(d6, 22n), U32.shln(d7, 1n)), U32.shln(d8, 24n)),
         U32.or(U32.shrn(d8, 8n), U32.shln(d9, 15n)),
         U32.or(U32.or(U32.shrn(d9, 17n), U32.shln(d10, 6n)), U32.shln(d11, 29n))}

# p[0] = 1. With m=-s0 mod 2^23, compute (t+a*b+m*p)/2^23.
def step(a: Digits, +b: U32, t: Digits) -> Digits:
  match a t:
    case D{a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11} D{t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11}:
      +s0 = Nat.add(U32.to_nat(t0), product(a0, b))
      +m = U32.and(U32.sub(0, low(s0)), 8388607)
      c0 = high(Nat.add(s0, U32.to_nat(m)))
      +s1 = Nat.add(Nat.add(Nat.add(U32.to_nat(t1), product(a1, b)), product(8388096, m)), c0)
      +s2 = Nat.add(Nat.add(Nat.add(U32.to_nat(t2), product(a2, b)), product(8126463, m)), high(s1))
      +s3 = Nat.add(Nat.add(Nat.add(U32.to_nat(t3), product(a3, b)), product(8385247, m)), high(s2))
      +s4 = Nat.add(Nat.add(Nat.add(U32.to_nat(t4), product(a4, b)), product(5914671, m)), high(s3))
      +s5 = Nat.add(Nat.add(Nat.add(U32.to_nat(t5), product(a5, b)), product(43639, m)), high(s4))
      +s6 = Nat.add(Nat.add(Nat.add(U32.to_nat(t6), product(a6, b)), product(157814, m)), high(s5))
      +s7 = Nat.add(Nat.add(Nat.add(U32.to_nat(t7), product(a7, b)), product(1895428, m)), high(s6))
      +s8 = Nat.add(Nat.add(Nat.add(U32.to_nat(t8), product(a8, b)), product(8210483, m)), high(s7))
      +s9 = Nat.add(Nat.add(Nat.add(U32.to_nat(t9), product(a9, b)), product(2511674, m)), high(s8))
      +s10 = Nat.add(Nat.add(Nat.add(U32.to_nat(t10), product(a10, b)), product(5224093, m)), high(s9))
      +s11 = Nat.add(Nat.add(Nat.add(U32.to_nat(t11), product(a11, b)), product(3, m)), high(s10))
      D{low(s1), low(s2), low(s3), low(s4), low(s5), low(s6), low(s7), low(s8), low(s9), low(s10), low(s11), U32.from_nat(high(s11))}

# Twelve fixed steps compute a*b/R, R=2^276, with no digit-list allocation.
def montgomery_digits(+a: Digits, b: Digits) -> Digits:
  match b:
    case D{b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11}:
      t0 = step(a, b0, digits(zero()))
      t1 = step(a, b1, t0)
      t2 = step(a, b2, t1)
      t3 = step(a, b3, t2)
      t4 = step(a, b4, t3)
      t5 = step(a, b5, t4)
      t6 = step(a, b6, t5)
      t7 = step(a, b7, t6)
      t8 = step(a, b8, t7)
      t9 = step(a, b9, t8)
      t10 = step(a, b10, t9)
      t11 = step(a, b11, t10)
      t11

# The result is below 2p < 2^256; one subtraction makes it canonical.
def montgomery(a: Scalar, b: Scalar) -> Scalar:
  reduce(from_digits(montgomery_digits(digits(a), digits(b))))

# R^2 modulo p, R=2^276.
def r_squared() -> Scalar:
  Fr{3924570556, 145767219, 778366792, 1273204038, 3903479135, 3648755039, 1443819439, 664944506}

# Prepared digits encode a*R mod p and are shared across a polynomial factor.
type Multiplier is Data:
  Prepared{digits: Digits}

def prepare(a: Scalar) -> Multiplier:
  Prepared{digits(montgomery(r_squared(), a))}

def multiply(m: Multiplier, b: Scalar) -> Scalar:
  match m:
    case Prepared{a}:
      reduce(from_digits(montgomery_digits(a, digits(b))))

def mul(a: Scalar, b: Scalar) -> Scalar:
  multiply(prepare(a), b)
