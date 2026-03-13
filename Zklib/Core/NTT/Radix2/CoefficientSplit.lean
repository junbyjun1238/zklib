import Zklib.Core.NTT.Radix2.Basic
import Zklib.Core.Polynomial.Parity

namespace Zklib.Core

namespace Radix2Domain

variable {F : Type*} [Monoid F]

/--
The natural-order lower-half embedding of `Fin halfSize` into a radix-2 domain.
-/
def lowerIndex (domain : Radix2Domain F) (h : 0 < domain.logSize)
    (i : Fin domain.halfSize) : Fin domain.size :=
  Fin.cast (domain.size_eq_halfSize_add_halfSize h).symm
    (Fin.castAdd domain.halfSize i)

/--
The natural-order upper-half embedding of `Fin halfSize` into a radix-2 domain.
-/
def upperIndex (domain : Radix2Domain F) (h : 0 < domain.logSize)
    (i : Fin domain.halfSize) : Fin domain.size :=
  Fin.cast (domain.size_eq_halfSize_add_halfSize h).symm
    (Fin.natAdd domain.halfSize i)

theorem point_lowerIndex (domain : Radix2Domain F) (h : 0 < domain.logSize)
    (i : Fin domain.halfSize) :
    domain.point (domain.lowerIndex h i) = domain.generator ^ (i : Nat) := by
  simp [EvaluationDomain.point, lowerIndex, Fin.val_cast, Fin.val_castAdd]

theorem point_upperIndex (domain : Radix2Domain F) (h : 0 < domain.logSize)
    (i : Fin domain.halfSize) :
    domain.point (domain.upperIndex h i) = domain.generator ^ (domain.halfSize + (i : Nat)) := by
  simp [EvaluationDomain.point, upperIndex, Fin.val_cast, Nat.add_comm]

theorem point_upperIndex_eq_generator_pow_half_mul_point_lowerIndex
    (domain : Radix2Domain F) (h : 0 < domain.logSize) (i : Fin domain.halfSize) :
    domain.point (domain.upperIndex h i) =
      domain.generator ^ domain.halfSize * domain.point (domain.lowerIndex h i) := by
  rw [point_upperIndex, point_lowerIndex, pow_add]

end Radix2Domain

namespace Radix2Domain

variable {F : Type*} [Field F]

theorem generator_pow_half_ne_one (domain : Radix2Domain F)
    (h : 0 < domain.logSize) :
    domain.generator ^ domain.halfSize ≠ 1 := by
  intro hpow
  have hlt : domain.halfSize < domain.size := by
    rw [domain.size_eq_halfSize_add_halfSize h]
    exact Nat.lt_add_of_pos_right domain.halfSize_pos
  let halfIdx : Fin domain.size := ⟨domain.halfSize, hlt⟩
  let zeroIdx : Fin domain.size := Fin.mk 0 domain.size_pos
  have heq : halfIdx = zeroIdx := by
    apply domain.generator_pow_injective
    simpa [halfIdx, zeroIdx] using hpow
  have hzero : domain.halfSize = 0 := by
    simpa [halfIdx, zeroIdx] using congrArg Fin.val heq
  exact (Nat.ne_of_gt domain.halfSize_pos) hzero

theorem generator_pow_half_eq_neg_one (domain : Radix2Domain F)
    (h : 0 < domain.logSize) :
    domain.generator ^ domain.halfSize = (-1 : F) := by
  have hsq : (domain.generator ^ domain.halfSize) ^ 2 = 1 := by
    calc
      (domain.generator ^ domain.halfSize) ^ 2
          = domain.generator ^ (domain.halfSize * 2) := by rw [← pow_mul]
      _ = domain.generator ^ domain.size := by
            rw [Nat.mul_comm, Nat.two_mul, domain.size_eq_halfSize_add_halfSize h]
      _ = 1 := domain.generator_pow_size_eq_one
  rcases sq_eq_one_iff.mp hsq with hone | hneg
  · exact (generator_pow_half_ne_one domain h hone).elim
  · exact hneg

theorem point_lowerIndex_sq_eq_halfDomain_point (domain : Radix2Domain F)
    (h : 0 < domain.logSize) (i : Fin domain.halfSize) :
    domain.point (domain.lowerIndex h i) ^ 2 = (domain.halfDomain h).point i := by
  rw [point_lowerIndex]
  change (domain.generator ^ (i : Nat)) ^ 2 = (domain.generator ^ 2) ^ (i : Nat)
  rw [← pow_mul]
  simpa [Nat.mul_comm] using (pow_mul domain.generator 2 (i : Nat))

theorem point_upperIndex_sq_eq_halfDomain_point (domain : Radix2Domain F)
    (h : 0 < domain.logSize) (i : Fin domain.halfSize) :
    domain.point (domain.upperIndex h i) ^ 2 = (domain.halfDomain h).point i := by
  rw [point_upperIndex]
  change (domain.generator ^ (domain.halfSize + (i : Nat))) ^ 2 =
    (domain.generator ^ 2) ^ (i : Nat)
  rw [← pow_mul]
  have hexp :
      (domain.halfSize + (i : Nat)) * 2 = domain.size + 2 * (i : Nat) := by
    calc
      (domain.halfSize + (i : Nat)) * 2
          = domain.halfSize * 2 + (i : Nat) * 2 := by rw [Nat.add_mul]
      _ = (domain.halfSize + domain.halfSize) + 2 * (i : Nat) := by
            rw [Nat.mul_two, Nat.mul_comm (i : Nat) 2]
      _ = domain.size + 2 * (i : Nat) := by
            rw [domain.size_eq_halfSize_add_halfSize h]
  rw [hexp, pow_add, domain.generator_pow_size_eq_one, one_mul, pow_mul]

theorem eval_lowerIndex_eq_evenOdd (domain : Radix2Domain F)
    (h : 0 < domain.logSize) (poly : Polynomial F) (i : Fin domain.halfSize) :
    poly.eval (domain.point (domain.lowerIndex h i)) =
      (PolynomialParity.evenPart poly).eval ((domain.halfDomain h).point i) +
      domain.point (domain.lowerIndex h i) *
        (PolynomialParity.oddPart poly).eval ((domain.halfDomain h).point i) := by
  rw [PolynomialParity.eval_evenPart_sq_add_oddPart_sq]
  rw [point_lowerIndex_sq_eq_halfDomain_point]

theorem eval_upperIndex_eq_evenOdd (domain : Radix2Domain F)
    (h : 0 < domain.logSize) (poly : Polynomial F) (i : Fin domain.halfSize) :
    poly.eval (domain.point (domain.upperIndex h i)) =
      (PolynomialParity.evenPart poly).eval ((domain.halfDomain h).point i) +
      domain.point (domain.upperIndex h i) *
        (PolynomialParity.oddPart poly).eval ((domain.halfDomain h).point i) := by
  rw [PolynomialParity.eval_evenPart_sq_add_oddPart_sq]
  rw [point_upperIndex_sq_eq_halfDomain_point]

theorem point_upperIndex_eq_neg_point_lowerIndex (domain : Radix2Domain F)
    (h : 0 < domain.logSize) (i : Fin domain.halfSize) :
    domain.point (domain.upperIndex h i) = -domain.point (domain.lowerIndex h i) := by
  rw [point_upperIndex_eq_generator_pow_half_mul_point_lowerIndex (domain := domain) h i,
    generator_pow_half_eq_neg_one (domain := domain) h]
  simp

theorem transform_lowerIndex_eq_evenOdd (domain : Radix2Domain F)
    (h : 0 < domain.logSize) (poly : Polynomial F) (i : Fin domain.halfSize) :
    domain.toNTTSpec.transform poly (domain.lowerIndex h i) =
      (domain.halfDomain h).toNTTSpec.transform (PolynomialParity.evenPart poly) i +
      domain.point (domain.lowerIndex h i) *
        (domain.halfDomain h).toNTTSpec.transform (PolynomialParity.oddPart poly) i := by
  change poly.eval (domain.point (domain.lowerIndex h i)) =
    (PolynomialParity.evenPart poly).eval ((domain.halfDomain h).point i) +
      domain.point (domain.lowerIndex h i) *
        (PolynomialParity.oddPart poly).eval ((domain.halfDomain h).point i)
  exact eval_lowerIndex_eq_evenOdd domain h poly i

theorem transform_upperIndex_eq_evenOdd (domain : Radix2Domain F)
    (h : 0 < domain.logSize) (poly : Polynomial F) (i : Fin domain.halfSize) :
    domain.toNTTSpec.transform poly (domain.upperIndex h i) =
      (domain.halfDomain h).toNTTSpec.transform (PolynomialParity.evenPart poly) i +
      domain.point (domain.upperIndex h i) *
        (domain.halfDomain h).toNTTSpec.transform (PolynomialParity.oddPart poly) i := by
  change poly.eval (domain.point (domain.upperIndex h i)) =
    (PolynomialParity.evenPart poly).eval ((domain.halfDomain h).point i) +
      domain.point (domain.upperIndex h i) *
        (PolynomialParity.oddPart poly).eval ((domain.halfDomain h).point i)
  exact eval_upperIndex_eq_evenOdd domain h poly i

theorem transform_upperIndex_eq_even_sub_twiddled_odd (domain : Radix2Domain F)
    (h : 0 < domain.logSize) (poly : Polynomial F) (i : Fin domain.halfSize) :
    domain.toNTTSpec.transform poly (domain.upperIndex h i) =
      (domain.halfDomain h).toNTTSpec.transform (PolynomialParity.evenPart poly) i -
      domain.point (domain.lowerIndex h i) *
        (domain.halfDomain h).toNTTSpec.transform (PolynomialParity.oddPart poly) i := by
  rw [transform_upperIndex_eq_evenOdd, point_upperIndex_eq_neg_point_lowerIndex]
  simp [sub_eq_add_neg]

theorem transform_naturalOrder_eq_butterflyValues (domain : Radix2Domain F)
    (h : 0 < domain.logSize) (poly : Polynomial F) :
    (fun i => domain.toNTTSpec.transform poly (domain.lowerIndex h i),
      fun i => domain.toNTTSpec.transform poly (domain.upperIndex h i)) =
      Radix2.butterflyValues
        (fun i => domain.point (domain.lowerIndex h i))
        ((domain.halfDomain h).toNTTSpec.transform (PolynomialParity.evenPart poly))
        ((domain.halfDomain h).toNTTSpec.transform (PolynomialParity.oddPart poly)) := by
  ext i <;> simp [Radix2.butterflyValues, transform_lowerIndex_eq_evenOdd,
    transform_upperIndex_eq_even_sub_twiddled_odd]

end Radix2Domain

end Zklib.Core
