import Zklib.Core.NTT.Radix2.CosetBasic

namespace Zklib.Core

namespace CosetRadix2Domain

variable {F : Type*} [Field F]

theorem transform_evenIndex_eq (domain : CosetRadix2Domain F) (h : 0 < domain.base.logSize)
    (poly : Polynomial F) (i : Fin domain.base.halfSize) :
    domain.toCosetNTTSpec.transform poly (domain.base.evenIndex h i) =
      (domain.halfEvenDomain h).toCosetNTTSpec.transform poly i := by
  change poly.eval (domain.point (domain.base.evenIndex h i)) =
    poly.eval ((domain.halfEvenDomain h).point i)
  rw [point_evenIndex_eq]

theorem transform_oddIndex_eq (domain : CosetRadix2Domain F) (h : 0 < domain.base.logSize)
    (poly : Polynomial F) (i : Fin domain.base.halfSize) :
    domain.toCosetNTTSpec.transform poly (domain.base.oddIndex h i) =
      (domain.halfOddDomain h).toCosetNTTSpec.transform poly i := by
  change poly.eval (domain.point (domain.base.oddIndex h i)) =
    poly.eval ((domain.halfOddDomain h).point i)
  rw [point_oddIndex_eq]

theorem evenValues_transform_eq_halfEvenDomain_transform (domain : CosetRadix2Domain F)
    (h : 0 < domain.base.logSize) (poly : Polynomial F) :
    domain.base.evenValues h (domain.toCosetNTTSpec.transform poly) =
      (domain.halfEvenDomain h).toCosetNTTSpec.transform poly := by
  funext i
  exact transform_evenIndex_eq domain h poly i

theorem oddValues_transform_eq_halfOddDomain_transform (domain : CosetRadix2Domain F)
    (h : 0 < domain.base.logSize) (poly : Polynomial F) :
    domain.base.oddValues h (domain.toCosetNTTSpec.transform poly) =
      (domain.halfOddDomain h).toCosetNTTSpec.transform poly := by
  funext i
  exact transform_oddIndex_eq domain h poly i

end CosetRadix2Domain

end Zklib.Core
