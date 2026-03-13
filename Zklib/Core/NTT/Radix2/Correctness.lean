import Zklib.Core.NTT.Correctness
import Zklib.Core.NTT.Radix2.Basic

namespace Zklib.Core

namespace Radix2

variable {alpha : Type*} {n : Nat}

theorem evenValues_apply (values : Fin (n + n) -> alpha) (i : Fin n) :
    evenValues values i = values (evenIndex n i) := by
  rfl

theorem oddValues_apply (values : Fin (n + n) -> alpha) (i : Fin n) :
    oddValues values i = values (oddIndex n i) := by
  rfl

variable {F : Type*} [Ring F] {omega a b : F} {twiddle even odd : Fin n -> F}

theorem butterfly_fst :
    (butterfly omega a b).1 = a + omega * b := by
  rfl

theorem butterfly_snd :
    (butterfly omega a b).2 = a - omega * b := by
  rfl

theorem butterflyValues_fst (i : Fin n) :
    (butterflyValues twiddle even odd).1 i = even i + twiddle i * odd i := by
  rfl

theorem butterflyValues_snd (i : Fin n) :
    (butterflyValues twiddle even odd).2 i = even i - twiddle i * odd i := by
  rfl

end Radix2

namespace Radix2Domain

variable {F : Type*} [Monoid F]

theorem halfDomain_point_eq_evenPoint (domain : Radix2Domain F) (h : 0 < domain.logSize)
    (i : Fin domain.halfSize) :
    (domain.halfDomain h).point i = domain.point (domain.evenIndex h i) := by
  change (domain.generator ^ 2) ^ (i : Nat) = domain.point (domain.evenIndex h i)
  rw [point_evenIndex]

end Radix2Domain

namespace Radix2Domain

variable {F : Type*} [Field F]

theorem transform_evenIndex_eq (domain : Radix2Domain F) (h : 0 < domain.logSize)
    (poly : Polynomial F) (i : Fin domain.halfSize) :
    domain.toNTTSpec.transform poly (domain.evenIndex h i) =
      poly.eval ((domain.generator ^ 2) ^ (i : Nat)) := by
  change poly.eval (domain.point (domain.evenIndex h i)) =
    poly.eval ((domain.generator ^ 2) ^ (i : Nat))
  rw [point_evenIndex]

theorem transform_oddIndex_eq (domain : Radix2Domain F) (h : 0 < domain.logSize)
    (poly : Polynomial F) (i : Fin domain.halfSize) :
    domain.toNTTSpec.transform poly (domain.oddIndex h i) =
      poly.eval ((domain.generator ^ 2) ^ (i : Nat) * domain.generator) := by
  change poly.eval (domain.point (domain.oddIndex h i)) =
    poly.eval ((domain.generator ^ 2) ^ (i : Nat) * domain.generator)
  rw [point_oddIndex]

theorem evenValues_transform_eq_halfDomain_transform (domain : Radix2Domain F)
    (h : 0 < domain.logSize) (poly : Polynomial F) :
    domain.evenValues h (domain.toNTTSpec.transform poly) =
      (domain.halfDomain h).toNTTSpec.transform poly := by
  funext i
  change poly.eval (domain.point (domain.evenIndex h i)) =
    poly.eval ((domain.halfDomain h).point i)
  rw [halfDomain_point_eq_evenPoint]

theorem oddValues_transform_eq_halfDomain_transform_twist (domain : Radix2Domain F)
    (h : 0 < domain.logSize) (poly : Polynomial F) :
    domain.oddValues h (domain.toNTTSpec.transform poly) =
      (domain.halfDomain h).toNTTSpec.transform (domain.twistPolynomial poly) := by
  funext i
  change poly.eval (domain.point (domain.oddIndex h i)) =
    (domain.twistPolynomial poly).eval ((domain.halfDomain h).point i)
  rw [Radix2Domain.eval_twistPolynomial, halfDomain_point_eq_evenPoint, point_evenIndex,
    point_oddIndex]

end Radix2Domain

end Zklib.Core
