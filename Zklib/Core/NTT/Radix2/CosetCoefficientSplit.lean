import Mathlib.Tactic.Linarith
import Zklib.Core.NTT.Radix2.CoefficientSplit
import Zklib.Core.NTT.Radix2.CosetBasic
import Zklib.Core.Polynomial.Parity

namespace Zklib.Core

namespace CosetRadix2Domain

variable {F : Type*} [Field F]

/--
The shift of a nontrivial radix-2 coset domain cannot vanish.

This is the field-level fact that lets the coefficient-recursive child domain
use the squared shift without collapsing distinct points.
-/
theorem shift_ne_zero (domain : CosetRadix2Domain F) (h : 0 < domain.base.logSize) :
    domain.shift ≠ 0 := by
  intro hshift
  have htwo : 1 < domain.base.size := by
    rw [domain.base.size_eq_halfSize_add_halfSize h]
    have hhalf : 0 < domain.base.halfSize := domain.base.halfSize_pos
    linarith
  let zeroIdx : Fin domain.base.size := Fin.mk 0 domain.base.size_pos
  let oneIdx : Fin domain.base.size := Fin.mk 1 htwo
  have heq : domain.point zeroIdx = domain.point oneIdx := by
    simp [CosetRadix2Domain.point, hshift]
  have hind : zeroIdx = oneIdx := domain.point_injective heq
  have hvals : (0 : Nat) = 1 := by
    simpa [zeroIdx, oneIdx] using congrArg Fin.val hind
  exact Nat.zero_ne_one hvals

/--
The coefficient-recursive child coset domain obtained by squaring the shift and
the generator.

This is the natural-order recursive domain for radix-2 Cooley-Tukey: evaluating
the even and odd coefficient halves happens on the squared points
`(shift * g^i)^2 = shift^2 * (g^2)^i`.
-/
def halfSquareDomain (domain : CosetRadix2Domain F) (h : 0 < domain.base.logSize) :
    CosetRadix2Domain F where
  base := domain.base.halfDomain h
  shift := domain.shift ^ 2
  shift_point_injective := by
    intro i j hij
    have hshiftSq : domain.shift ^ 2 ≠ 0 := by
      exact pow_ne_zero 2 (domain.shift_ne_zero h)
    have hpoint :
        (domain.base.halfDomain h).point i = (domain.base.halfDomain h).point j := by
      exact mul_left_cancel₀ hshiftSq hij
    exact (domain.base.halfDomain h).point_injective hpoint

/--
The canonical squared-shift child used in a successor-step coefficient
recursion.
-/
def succHalfSquare (domain : CosetRadix2Domain F) {k : Nat}
    (hk : domain.base.logSize = k + 1) : CosetRadix2Domain F :=
  domain.halfSquareDomain (by simp [hk])

@[simp] theorem succHalfSquare_logSize (domain : CosetRadix2Domain F) {k : Nat}
    (hk : domain.base.logSize = k + 1) :
    (domain.succHalfSquare hk).base.logSize = k := by
  simp [succHalfSquare, CosetRadix2Domain.halfSquareDomain, Radix2Domain.halfDomain, hk]

theorem point_lowerIndex_sq_eq_halfSquareDomain_point (domain : CosetRadix2Domain F)
    (h : 0 < domain.base.logSize) (i : Fin domain.base.halfSize) :
    domain.point (domain.base.lowerIndex h i) ^ 2 = (domain.halfSquareDomain h).point i := by
  calc
    domain.point (domain.base.lowerIndex h i) ^ 2
        = (domain.shift * domain.base.point (domain.base.lowerIndex h i)) ^ 2 := by
            rfl
    _ = domain.shift ^ 2 * (domain.base.point (domain.base.lowerIndex h i) ^ 2) := by
          rw [mul_pow]
    _ = domain.shift ^ 2 * (domain.base.halfDomain h).point i := by
          rw [domain.base.point_lowerIndex_sq_eq_halfDomain_point h i]
    _ = (domain.halfSquareDomain h).point i := by
          rfl

theorem point_upperIndex_sq_eq_halfSquareDomain_point (domain : CosetRadix2Domain F)
    (h : 0 < domain.base.logSize) (i : Fin domain.base.halfSize) :
    domain.point (domain.base.upperIndex h i) ^ 2 = (domain.halfSquareDomain h).point i := by
  calc
    domain.point (domain.base.upperIndex h i) ^ 2
        = (domain.shift * domain.base.point (domain.base.upperIndex h i)) ^ 2 := by
            rfl
    _ = domain.shift ^ 2 * (domain.base.point (domain.base.upperIndex h i) ^ 2) := by
          rw [mul_pow]
    _ = domain.shift ^ 2 * (domain.base.halfDomain h).point i := by
          rw [domain.base.point_upperIndex_sq_eq_halfDomain_point h i]
    _ = (domain.halfSquareDomain h).point i := by
          rfl

theorem eval_lowerIndex_eq_evenOdd (domain : CosetRadix2Domain F)
    (h : 0 < domain.base.logSize) (poly : Polynomial F) (i : Fin domain.base.halfSize) :
    poly.eval (domain.point (domain.base.lowerIndex h i)) =
      (PolynomialParity.evenPart poly).eval ((domain.halfSquareDomain h).point i) +
      domain.point (domain.base.lowerIndex h i) *
        (PolynomialParity.oddPart poly).eval ((domain.halfSquareDomain h).point i) := by
  rw [PolynomialParity.eval_evenPart_sq_add_oddPart_sq]
  rw [domain.point_lowerIndex_sq_eq_halfSquareDomain_point h i]

theorem eval_upperIndex_eq_evenOdd (domain : CosetRadix2Domain F)
    (h : 0 < domain.base.logSize) (poly : Polynomial F) (i : Fin domain.base.halfSize) :
    poly.eval (domain.point (domain.base.upperIndex h i)) =
      (PolynomialParity.evenPart poly).eval ((domain.halfSquareDomain h).point i) +
      domain.point (domain.base.upperIndex h i) *
        (PolynomialParity.oddPart poly).eval ((domain.halfSquareDomain h).point i) := by
  rw [PolynomialParity.eval_evenPart_sq_add_oddPart_sq]
  rw [domain.point_upperIndex_sq_eq_halfSquareDomain_point h i]

theorem point_upperIndex_eq_neg_point_lowerIndex (domain : CosetRadix2Domain F)
    (h : 0 < domain.base.logSize) (i : Fin domain.base.halfSize) :
    domain.point (domain.base.upperIndex h i) = -domain.point (domain.base.lowerIndex h i) := by
  rw [CosetRadix2Domain.point, CosetRadix2Domain.point,
    domain.base.point_upperIndex_eq_neg_point_lowerIndex h i]
  simp

theorem transform_lowerIndex_eq_evenOdd (domain : CosetRadix2Domain F)
    (h : 0 < domain.base.logSize) (poly : Polynomial F) (i : Fin domain.base.halfSize) :
    domain.toCosetNTTSpec.transform poly (domain.base.lowerIndex h i) =
      (domain.halfSquareDomain h).toCosetNTTSpec.transform (PolynomialParity.evenPart poly) i +
      domain.point (domain.base.lowerIndex h i) *
        (domain.halfSquareDomain h).toCosetNTTSpec.transform (PolynomialParity.oddPart poly) i := by
  change poly.eval (domain.point (domain.base.lowerIndex h i)) =
    (PolynomialParity.evenPart poly).eval ((domain.halfSquareDomain h).point i) +
      domain.point (domain.base.lowerIndex h i) *
        (PolynomialParity.oddPart poly).eval ((domain.halfSquareDomain h).point i)
  exact domain.eval_lowerIndex_eq_evenOdd h poly i

theorem transform_upperIndex_eq_evenOdd (domain : CosetRadix2Domain F)
    (h : 0 < domain.base.logSize) (poly : Polynomial F) (i : Fin domain.base.halfSize) :
    domain.toCosetNTTSpec.transform poly (domain.base.upperIndex h i) =
      (domain.halfSquareDomain h).toCosetNTTSpec.transform (PolynomialParity.evenPart poly) i +
      domain.point (domain.base.upperIndex h i) *
        (domain.halfSquareDomain h).toCosetNTTSpec.transform (PolynomialParity.oddPart poly) i := by
  change poly.eval (domain.point (domain.base.upperIndex h i)) =
    (PolynomialParity.evenPart poly).eval ((domain.halfSquareDomain h).point i) +
      domain.point (domain.base.upperIndex h i) *
        (PolynomialParity.oddPart poly).eval ((domain.halfSquareDomain h).point i)
  exact domain.eval_upperIndex_eq_evenOdd h poly i

theorem transform_upperIndex_eq_even_sub_twiddled_odd (domain : CosetRadix2Domain F)
    (h : 0 < domain.base.logSize) (poly : Polynomial F) (i : Fin domain.base.halfSize) :
    domain.toCosetNTTSpec.transform poly (domain.base.upperIndex h i) =
      (domain.halfSquareDomain h).toCosetNTTSpec.transform (PolynomialParity.evenPart poly) i -
      domain.point (domain.base.lowerIndex h i) *
        (domain.halfSquareDomain h).toCosetNTTSpec.transform (PolynomialParity.oddPart poly) i := by
  rw [domain.transform_upperIndex_eq_evenOdd h poly i, domain.point_upperIndex_eq_neg_point_lowerIndex h i]
  simp [sub_eq_add_neg]

theorem transform_naturalOrder_eq_butterflyValues (domain : CosetRadix2Domain F)
    (h : 0 < domain.base.logSize) (poly : Polynomial F) :
    (fun i => domain.toCosetNTTSpec.transform poly (domain.base.lowerIndex h i),
      fun i => domain.toCosetNTTSpec.transform poly (domain.base.upperIndex h i)) =
      Radix2.butterflyValues
        (fun i => domain.point (domain.base.lowerIndex h i))
        ((domain.halfSquareDomain h).toCosetNTTSpec.transform (PolynomialParity.evenPart poly))
        ((domain.halfSquareDomain h).toCosetNTTSpec.transform (PolynomialParity.oddPart poly)) := by
  ext i <;> simp [Radix2.butterflyValues, domain.transform_lowerIndex_eq_evenOdd,
    domain.transform_upperIndex_eq_even_sub_twiddled_odd]

end CosetRadix2Domain

end Zklib.Core
