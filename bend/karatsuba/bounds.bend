# Proof by reflection over the finite API size bound, not over scalar inputs.
# Every scalar value is still universally quantified by shape.bend.
import Base
import ./shape.bend as Shape

# False and True are disjoint constructors; no axiom is used for elimination.
def truth_type(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

def false_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : truth_type(_)
  Unit{}

def absurd(-A: Type, e: Empty) -> A:
  match e:

def and_left(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool})
  -> {a == True{} : Bool}:
  match a:
    case False{}:
      absurd({False{} == True{} : Bool}, false_true(e))
    case True{}:
      {==}

def and_right(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool})
  -> {b == True{} : Bool}:
  match a:
    case False{}:
      absurd({b == True{} : Bool}, false_true(e))
    case True{}:
      e

def equal_nat(a: Nat, b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+p:
      absurd({0n == 1n+p : Nat}, false_true(e))
    case 1n+p 0n:
      absurd({1n+p == 0n : Nat}, false_true(e))
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, k => 1n+k, p, q, equal_nat(p, q, e))

def below_zero(n: Nat, e: {Nat.is_lt(n, 0n) == True{} : Bool}) -> Empty:
  match n:
    case 0n:
      false_true(e)
    case 1n+p:
      false_true(e)

def add_next(n: Nat, -m: Nat) -> {Nat.add(n, 1n+m) == 1n+Nat.add(n, m) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, k => 1n+k, Nat.add(p, 1n+m), 1n+Nat.add(p, m), add_next(p, m))

def add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, k => 1n+k, Nat.add(p, 0n), p, add_zero(p))

def property(+n: Nat) -> Bool:
  Nat.is_eq(Shape.coefficients_size(n), 1n+n)

def check_range(count: Nat, +start: Nat) -> Bool:
  match count:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(property(start), check_range(p, 1n+start))

def split_and(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool})
  -> {a == True{} : Bool} & {b == True{} : Bool}:
  match a:
    case False{}:
      absurd({False{} == True{} : Bool} & {b == True{} : Bool}, false_true(e))
    case True{}:
      ({==}, e)

def prepend_checked(-start: Nat, -count: Nat, head: {property(start) == True{} : Bool},
                    tail: {check_range(count, 1n+start) == True{} : Bool})
  -> {check_range(1n+count, start) == True{} : Bool}:
  Equal.trans(Bool, Bool.and(property(start), check_range(count, 1n+start)),
    check_range(count, 1n+start), True{},
    Equal.cong(Bool, Bool, b => Bool.and(b, check_range(count, 1n+start)), property(start), True{}, head), tail)

def move_right(p: Nat, -start: Nat, -count: Nat,
               e: {check_range(count, Nat.add(1n+p, start)) == True{} : Bool})
  -> {check_range(count, Nat.add(p, 1n+start)) == True{} : Bool}:
  Equal.trans(Bool, check_range(count, Nat.add(p, 1n+start)), check_range(count, 1n+Nat.add(p, start)), True{},
    Equal.cong(Nat, Bool, n => check_range(count, n), Nat.add(p, 1n+start), 1n+Nat.add(p, start), add_next(p, start)), e)

def append_step(-start: Nat, -left: Nat, -right: Nat,
                pieces: {property(start) == True{} : Bool} & {check_range(left, 1n+start) == True{} : Bool},
                finish: {check_range(left, 1n+start) == True{} : Bool} -> {check_range(Nat.add(left, right), 1n+start) == True{} : Bool})
  -> {check_range(1n+Nat.add(left, right), start) == True{} : Bool}:
  match pieces:
    case Tuple{head, tail}:
      prepend_checked(start, Nat.add(left, right), head, finish(tail))

def append_checked(left: Nat, +right: Nat, +start: Nat,
                   first: {check_range(left, start) == True{} : Bool},
                   second: {check_range(right, Nat.add(left, start)) == True{} : Bool})
  -> {check_range(Nat.add(left, right), start) == True{} : Bool}:
  match left:
    case 0n:
      second
    case 1n++p:
      append_step(start, p, right, split_and(property(start), check_range(p, 1n+start), first),
        tail => append_checked(p, right, 1n+start, tail, move_right(p, start, right, second)))

# Keep arithmetic on indices out of the Boolean normalization: otherwise the
# kernel expands the entire range just to compare two equivalent index terms.
def append_concrete(+left: Nat, +right: Nat, +start: Nat, -total: Nat, -next: Nat,
                    total_eq: {Nat.add(left, right) == total : Nat},
                    next_eq: {Nat.add(left, start) == next : Nat},
                    first: {check_range(left, start) == True{} : Bool},
                    second: {check_range(right, next) == True{} : Bool})
  -> {check_range(total, start) == True{} : Bool}:
  %total_eq : {check_range(_, start) == True{} : Bool}
  append_checked(left, right, start, first,
    Equal.trans(Bool, check_range(right, Nat.add(left, start)), check_range(right, next), True{},
      Equal.cong(Nat, Bool, n => check_range(right, n), Nat.add(left, start), next, next_eq), second))

# Split the closed computation into small certificates to stay within BendTT's
# per-definition reduction budget. Their checked concatenation covers 0..256.
def sizes_000() -> {check_range(16n, 0n) == True{} : Bool}:
  {==}

def sizes_016() -> {check_range(16n, 16n) == True{} : Bool}:
  {==}

def sizes_032() -> {check_range(16n, 32n) == True{} : Bool}:
  {==}

def sizes_048() -> {check_range(16n, 48n) == True{} : Bool}:
  {==}

def sizes_064() -> {check_range(16n, 64n) == True{} : Bool}:
  {==}

def sizes_080() -> {check_range(16n, 80n) == True{} : Bool}:
  {==}

def sizes_096() -> {check_range(16n, 96n) == True{} : Bool}:
  {==}

def sizes_112() -> {check_range(16n, 112n) == True{} : Bool}:
  {==}

def sizes_128() -> {check_range(16n, 128n) == True{} : Bool}:
  {==}

def sizes_144() -> {check_range(16n, 144n) == True{} : Bool}:
  {==}

def sizes_160() -> {check_range(16n, 160n) == True{} : Bool}:
  {==}

def sizes_176() -> {check_range(16n, 176n) == True{} : Bool}:
  {==}

def sizes_192() -> {check_range(16n, 192n) == True{} : Bool}:
  {==}

def sizes_208() -> {check_range(16n, 208n) == True{} : Bool}:
  {==}

def sizes_224() -> {check_range(16n, 224n) == True{} : Bool}:
  {==}

def sizes_240() -> {check_range(16n, 240n) == True{} : Bool}:
  {==}

def sizes_256() -> {check_range(1n, 256n) == True{} : Bool}:
  {==}

def checked_range() -> {check_range(257n, 0n) == True{} : Bool}:
  append_concrete(16n, 241n, 0n, 257n, 16n, {==}, {==}, sizes_000(),
    append_concrete(16n, 225n, 16n, 241n, 32n, {==}, {==}, sizes_016(),
      append_concrete(16n, 209n, 32n, 225n, 48n, {==}, {==}, sizes_032(),
        append_concrete(16n, 193n, 48n, 209n, 64n, {==}, {==}, sizes_048(),
          append_concrete(16n, 177n, 64n, 193n, 80n, {==}, {==}, sizes_064(),
            append_concrete(16n, 161n, 80n, 177n, 96n, {==}, {==}, sizes_080(),
              append_concrete(16n, 145n, 96n, 161n, 112n, {==}, {==}, sizes_096(),
                append_concrete(16n, 129n, 112n, 145n, 128n, {==}, {==}, sizes_112(),
                  append_concrete(16n, 113n, 128n, 129n, 144n, {==}, {==}, sizes_128(),
                    append_concrete(16n, 97n, 144n, 113n, 160n, {==}, {==}, sizes_144(),
                      append_concrete(16n, 81n, 160n, 97n, 176n, {==}, {==}, sizes_160(),
                        append_concrete(16n, 65n, 176n, 81n, 192n, {==}, {==}, sizes_176(),
                          append_concrete(16n, 49n, 192n, 65n, 208n, {==}, {==}, sizes_192(),
                            append_concrete(16n, 33n, 208n, 49n, 224n, {==}, {==}, sizes_208(),
                              append_concrete(16n, 17n, 224n, 33n, 240n, {==}, {==}, sizes_224(),
                                append_concrete(16n, 1n, 240n, 17n, 256n, {==}, {==}, sizes_240(),
                                  sizes_256()))))))))))))))))

def checked_at(count: Nat, index: Nat, +start: Nat,
               bound: {Nat.is_lt(index, count) == True{} : Bool},
               checked: {check_range(count, start) == True{} : Bool})
  -> {property(Nat.add(index, start)) == True{} : Bool}:
  match count:
    case 0n:
      absurd({property(Nat.add(index, start)) == True{} : Bool}, below_zero(index, bound))
    case 1n++p:
      match index:
        case 0n:
          and_left(property(start), check_range(p, 1n+start), checked)
        case 1n++k:
          %add_next(k, start) : {property(_) == True{} : Bool}
          checked_at(p, k, 1n+start, bound,
            and_right(property(start), check_range(p, 1n+start), checked))

def coefficient_count(+n: Nat, bound: {Nat.is_lt(n, 257n) == True{} : Bool})
  -> {Shape.coefficients_size(n) == 1n+n : Nat}:
  equal_nat(Shape.coefficients_size(n), 1n+n,
    %add_zero(n) : {property(_) == True{} : Bool}
    checked_at(257n, n, 0n, bound, checked_range()))
