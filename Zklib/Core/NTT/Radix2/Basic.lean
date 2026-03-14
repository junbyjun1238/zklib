import Mathlib.Tactic.Linarith
import Zklib.Core.NTT.Basic

namespace Zklib.Core

namespace Radix2

/--
The even-position embedding from `Fin n` into `Fin (n + n)`.
-/
def evenIndex (n : Nat) (i : Fin n) : Fin (n + n) :=
  ⟨(i : Nat) + i, Nat.add_lt_add i.isLt i.isLt⟩

/--
The odd-position embedding from `Fin n` into `Fin (n + n)`.
-/
def oddIndex (n : Nat) (i : Fin n) : Fin (n + n) :=
  ⟨(i : Nat) + (i + 1),
    Nat.add_lt_add_of_lt_of_le i.isLt (Nat.succ_le_of_lt i.isLt)⟩

/--
Restrict a length-`2n` table to its even positions.
-/
def evenValues {alpha : Type*} {n : Nat} (values : Fin (n + n) -> alpha) :
    Fin n -> alpha :=
  fun i => values (evenIndex n i)

/--
Restrict a length-`2n` table to its odd positions.
-/
def oddValues {alpha : Type*} {n : Nat} (values : Fin (n + n) -> alpha) :
    Fin n -> alpha :=
  fun i => values (oddIndex n i)

theorem evenIndex_injective (n : Nat) : Function.Injective (evenIndex n) := by
  intro i j hij
  apply Fin.ext
  have hvals : ((i : Nat) + i) = ((j : Nat) + j) := congrArg Fin.val hij
  nlinarith

theorem oddIndex_injective (n : Nat) : Function.Injective (oddIndex n) := by
  intro i j hij
  apply Fin.ext
  have hvals : ((i : Nat) + (i + 1)) = ((j : Nat) + (j + 1)) := congrArg Fin.val hij
  nlinarith

/--
The pointwise butterfly used by radix-2 FFT stages.
-/
def butterfly {F : Type*} [Ring F] (omega a b : F) : F × F :=
  (a + omega * b, a - omega * b)

/--
Apply the radix-2 butterfly pointwise to a pair of half-size tables.
-/
def butterflyValues {F : Type*} [Ring F] {n : Nat}
    (twiddle even odd : Fin n -> F) : (Fin n -> F) × (Fin n -> F) :=
  (fun i => even i + twiddle i * odd i,
   fun i => even i - twiddle i * odd i)

end Radix2

/--
A radix-2 evaluation domain is an evaluation domain whose size is a power of
two. This is the domain class needed for Cooley-Tukey style decomposition.
-/
structure Radix2Domain (F : Type*) [Monoid F] extends EvaluationDomain F where
  logSize : Nat
  size_eq_pow : size = 2 ^ logSize

namespace Radix2Domain

variable {F : Type*} [Monoid F]

/--
The half-size of a radix-2 domain, exposed in a way that is stable under a
single recursive descent.
-/
def halfSize (domain : Radix2Domain F) : Nat :=
  2 ^ domain.logSize.pred

theorem size_eq_halfSize_add_halfSize (domain : Radix2Domain F)
    (h : 0 < domain.logSize) :
    domain.size = domain.halfSize + domain.halfSize := by
  have hne : domain.logSize ≠ 0 := Nat.ne_of_gt h
  rcases Nat.exists_eq_succ_of_ne_zero hne with ⟨k, hk⟩
  simp [halfSize, domain.size_eq_pow, hk, pow_succ, Nat.mul_two]

theorem halfSize_pos (domain : Radix2Domain F) :
    0 < domain.halfSize := by
  simp [halfSize]

/--
The even-position points in a radix-2 domain.
-/
def evenIndex (domain : Radix2Domain F) (h : 0 < domain.logSize)
    (i : Fin domain.halfSize) : Fin domain.size :=
  ⟨(i : Nat) + i, by
    have hi : (i : Nat) + i < domain.halfSize + domain.halfSize :=
      Nat.add_lt_add i.isLt i.isLt
    simpa [size_eq_halfSize_add_halfSize domain h] using hi⟩

/--
The odd-position points in a radix-2 domain.
-/
def oddIndex (domain : Radix2Domain F) (h : 0 < domain.logSize)
    (i : Fin domain.halfSize) : Fin domain.size :=
  ⟨(i : Nat) + (i + 1), by
    have hi : (i : Nat) + (i + 1) < domain.halfSize + domain.halfSize :=
      Nat.add_lt_add_of_lt_of_le i.isLt (Nat.succ_le_of_lt i.isLt)
    simpa [size_eq_halfSize_add_halfSize domain h] using hi⟩

/--
The even-indexed restriction of a domain-sized table.
-/
def evenValues (domain : Radix2Domain F) (h : 0 < domain.logSize)
    {alpha : Type*} (values : Fin domain.size -> alpha) : Fin domain.halfSize -> alpha :=
  fun i => values (domain.evenIndex h i)

/--
The odd-indexed restriction of a domain-sized table.
-/
def oddValues (domain : Radix2Domain F) (h : 0 < domain.logSize)
    {alpha : Type*} (values : Fin domain.size -> alpha) : Fin domain.halfSize -> alpha :=
  fun i => values (domain.oddIndex h i)

theorem evenIndex_injective (domain : Radix2Domain F) (h : 0 < domain.logSize) :
    Function.Injective (domain.evenIndex h) := by
  intro i j hij
  apply Fin.ext
  have hvals : ((i : Nat) + i) = ((j : Nat) + j) := congrArg Fin.val hij
  nlinarith

theorem oddIndex_injective (domain : Radix2Domain F) (h : 0 < domain.logSize) :
    Function.Injective (domain.oddIndex h) := by
  intro i j hij
  apply Fin.ext
  have hvals : ((i : Nat) + (i + 1)) = ((j : Nat) + (j + 1)) := congrArg Fin.val hij
  nlinarith

theorem point_evenIndex (domain : Radix2Domain F) (h : 0 < domain.logSize)
    (i : Fin domain.halfSize) :
    domain.point (domain.evenIndex h i) = (domain.generator ^ 2) ^ (i : Nat) := by
  simpa [EvaluationDomain.point, evenIndex, Nat.two_mul] using
    (pow_mul domain.generator 2 (i : Nat))

theorem point_oddIndex (domain : Radix2Domain F) (h : 0 < domain.logSize)
    (i : Fin domain.halfSize) :
    domain.point (domain.oddIndex h i) = (domain.generator ^ 2) ^ (i : Nat) * domain.generator := by
  have hindex : (i : Nat) + (i + 1) = 2 * (i : Nat) + 1 := by
    rw [Nat.two_mul]
    simp [Nat.add_assoc]
  change domain.generator ^ ((i : Nat) + (i + 1)) =
    (domain.generator ^ 2) ^ (i : Nat) * domain.generator
  rw [hindex, pow_add, pow_one, pow_mul]

/--
The recursive radix-2 subdomain obtained by squaring the generator.
-/
def halfDomain (domain : Radix2Domain F) (h : 0 < domain.logSize) : Radix2Domain F where
  toEvaluationDomain :=
    { size := domain.halfSize
      size_pos := domain.halfSize_pos
      generator := domain.generator ^ 2
      generator_pow_size_eq_one := by
        have hsize : domain.size = 2 * domain.halfSize := by
          rw [size_eq_halfSize_add_halfSize domain h, ← Nat.two_mul]
        calc
          (domain.generator ^ 2) ^ domain.halfSize = domain.generator ^ (2 * domain.halfSize) := by
            rw [pow_mul]
          _ = domain.generator ^ domain.size := by rw [hsize]
          _ = 1 := domain.generator_pow_size_eq_one
      generator_pow_injective := by
        intro i j hij
        have hpoint :
            domain.point (domain.evenIndex h i) = domain.point (domain.evenIndex h j) := by
          simpa [point_evenIndex] using hij
        have heq : domain.evenIndex h i = domain.evenIndex h j := domain.point_injective hpoint
        exact domain.evenIndex_injective h heq }
  logSize := domain.logSize.pred
  size_eq_pow := rfl

/--
The canonical child domain used in a successor-step radix-2 recursion.

Packaging the positivity proof here keeps downstream recursive proofs from
rebuilding the same shape witnesses at every call site.
-/
def succHalf (domain : Radix2Domain F) {k : Nat} (hk : domain.logSize = k + 1) :
    Radix2Domain F :=
  domain.halfDomain (by simp [hk])

@[simp] theorem succHalf_logSize (domain : Radix2Domain F) {k : Nat}
    (hk : domain.logSize = k + 1) :
    (domain.succHalf hk).logSize = k := by
  simp [succHalf, Radix2Domain.halfDomain, hk]

@[simp] theorem succHalf_size (domain : Radix2Domain F) {k : Nat}
    (hk : domain.logSize = k + 1) :
    (domain.succHalf hk).size = domain.halfSize := by
  rfl

end Radix2Domain

namespace Radix2Domain

variable {F : Type*} [Field F]

/--
The semantic NTT attached to a radix-2 domain.
-/
noncomputable def toNTTSpec (domain : Radix2Domain F) : NTTSpec F :=
  NTTSpec.mathlib domain.toEvaluationDomain

/--
Twist a polynomial by the domain generator. This is the polynomial whose
evaluation at `x` is the original evaluation at `x * generator`.
-/
noncomputable def twistPolynomial (domain : Radix2Domain F) (poly : Polynomial F) : Polynomial F :=
  poly.comp (Polynomial.X * Polynomial.C domain.generator)

theorem eval_twistPolynomial (domain : Radix2Domain F) (poly : Polynomial F) (x : F) :
    (domain.twistPolynomial poly).eval x = poly.eval (x * domain.generator) := by
  rw [twistPolynomial, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C]

end Radix2Domain

end Zklib.Core
