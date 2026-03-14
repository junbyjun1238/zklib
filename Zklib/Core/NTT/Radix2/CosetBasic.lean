import Zklib.Core.NTT.Radix2.Basic

namespace Zklib.Core

/--
A radix-2 coset domain is a shifted radix-2 base domain whose shifted points
remain injective.

This is the domain class needed for coset FFT recursion. The base domain
controls the radix-2 structure, while the shift distinguishes the even/odd
recursive branches.
-/
structure CosetRadix2Domain (F : Type*) [CommMonoid F] where
  base : Radix2Domain F
  shift : F
  shift_point_injective : Function.Injective (fun i : Fin base.size => shift * base.point i)

namespace CosetRadix2Domain

variable {F : Type*} [CommMonoid F]

/--
Forget the radix-2 structure and view a coset radix-2 domain as a generic
coset evaluation domain.
-/
def toCosetEvaluationDomain (domain : CosetRadix2Domain F) : CosetEvaluationDomain F where
  base := domain.base.toEvaluationDomain
  shift := domain.shift
  shift_point_injective := domain.shift_point_injective

/--
The canonical enumeration of shifted radix-2 points.
-/
def point (domain : CosetRadix2Domain F) (i : Fin domain.base.size) : F :=
  domain.shift * domain.base.point i

/--
The recursive even-branch coset domain.
-/
def halfEvenDomain (domain : CosetRadix2Domain F) (h : 0 < domain.base.logSize) :
    CosetRadix2Domain F where
  base := domain.base.halfDomain h
  shift := domain.shift
  shift_point_injective := by
    intro i j hij
    have hbase :
        domain.shift * domain.base.point (domain.base.evenIndex h i) =
          domain.shift * domain.base.point (domain.base.evenIndex h j) := by
      rw [domain.base.point_evenIndex, domain.base.point_evenIndex]
      simpa [point] using hij
    have hind : domain.base.evenIndex h i = domain.base.evenIndex h j :=
      domain.shift_point_injective hbase
    exact domain.base.evenIndex_injective h hind

/--
The recursive odd-branch coset domain.
-/
def halfOddDomain (domain : CosetRadix2Domain F) (h : 0 < domain.base.logSize) :
    CosetRadix2Domain F where
  base := domain.base.halfDomain h
  shift := domain.shift * domain.base.generator
  shift_point_injective := by
    intro i j hij
    have hbase :
        domain.shift * domain.base.point (domain.base.oddIndex h i) =
          domain.shift * domain.base.point (domain.base.oddIndex h j) := by
      calc
        domain.shift * domain.base.point (domain.base.oddIndex h i)
            = (domain.shift * domain.base.generator) * (domain.base.halfDomain h).point i := by
                rw [domain.base.point_oddIndex]
                change domain.shift * (((domain.base.generator ^ 2) ^ (i : Nat)) * domain.base.generator) =
                  (domain.shift * domain.base.generator) * ((domain.base.generator ^ 2) ^ (i : Nat))
                simp [mul_assoc, mul_comm]
        _ = (domain.shift * domain.base.generator) * (domain.base.halfDomain h).point j := hij
        _ = domain.shift * domain.base.point (domain.base.oddIndex h j) := by
                rw [domain.base.point_oddIndex]
                change (domain.shift * domain.base.generator) * ((domain.base.generator ^ 2) ^ (j : Nat)) =
                  domain.shift * (((domain.base.generator ^ 2) ^ (j : Nat)) * domain.base.generator)
                simp [mul_assoc, mul_comm]
    have hind : domain.base.oddIndex h i = domain.base.oddIndex h j :=
      domain.shift_point_injective hbase
    exact domain.base.oddIndex_injective h hind

theorem point_eq_shift_mul (domain : CosetRadix2Domain F) (i : Fin domain.base.size) :
    domain.point i = domain.shift * domain.base.point i := by
  rfl

theorem point_zero_eq_shift (domain : CosetRadix2Domain F) :
    domain.point (Fin.mk 0 domain.base.size_pos) = domain.shift := by
  simp [point, domain.base.point_zero_eq_one]

theorem point_injective (domain : CosetRadix2Domain F) :
    Function.Injective domain.point := by
  simpa [point] using domain.shift_point_injective

theorem point_evenIndex_eq (domain : CosetRadix2Domain F) (h : 0 < domain.base.logSize)
    (i : Fin domain.base.halfSize) :
    domain.point (domain.base.evenIndex h i) = (domain.halfEvenDomain h).point i := by
  rw [point, point, domain.base.point_evenIndex]
  rfl

theorem point_oddIndex_eq (domain : CosetRadix2Domain F) (h : 0 < domain.base.logSize)
    (i : Fin domain.base.halfSize) :
    domain.point (domain.base.oddIndex h i) = (domain.halfOddDomain h).point i := by
  rw [point, point, domain.base.point_oddIndex]
  change domain.shift * (((domain.base.generator ^ 2) ^ (i : Nat)) * domain.base.generator) =
    (domain.shift * domain.base.generator) * ((domain.base.generator ^ 2) ^ (i : Nat))
  simp [mul_assoc, mul_comm]

/--
The canonical even child used in a successor-step parity recursion.
-/
def succHalfEven (domain : CosetRadix2Domain F) {k : Nat}
    (hk : domain.base.logSize = k + 1) : CosetRadix2Domain F :=
  domain.halfEvenDomain (by simp [hk])

/--
The canonical odd child used in a successor-step parity recursion.
-/
def succHalfOdd (domain : CosetRadix2Domain F) {k : Nat}
    (hk : domain.base.logSize = k + 1) : CosetRadix2Domain F :=
  domain.halfOddDomain (by simp [hk])

@[simp] theorem succHalfEven_logSize (domain : CosetRadix2Domain F) {k : Nat}
    (hk : domain.base.logSize = k + 1) :
    (domain.succHalfEven hk).base.logSize = k := by
  simp [succHalfEven, CosetRadix2Domain.halfEvenDomain, Radix2Domain.halfDomain, hk]

@[simp] theorem succHalfOdd_logSize (domain : CosetRadix2Domain F) {k : Nat}
    (hk : domain.base.logSize = k + 1) :
    (domain.succHalfOdd hk).base.logSize = k := by
  simp [succHalfOdd, CosetRadix2Domain.halfOddDomain, Radix2Domain.halfDomain, hk]

end CosetRadix2Domain

namespace CosetRadix2Domain

variable {F : Type*} [Field F]

/--
The semantic coset-NTT attached to a radix-2 coset domain.
-/
noncomputable def toCosetNTTSpec (domain : CosetRadix2Domain F) : CosetNTTSpec F :=
  CosetNTTSpec.mathlib domain.toCosetEvaluationDomain

end CosetRadix2Domain

end Zklib.Core
