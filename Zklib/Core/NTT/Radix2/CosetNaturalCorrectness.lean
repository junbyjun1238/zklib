import Zklib.Core.NTT.Radix2.CosetNatural

namespace Zklib.Core

namespace CosetRadix2Domain

variable {F : Type*} [Field F]

theorem fftNatural_lowerIndex_eq_transform (domain : CosetRadix2Domain F)
    (h : 0 < domain.base.logSize) (poly : Polynomial F) (i : Fin domain.base.halfSize) :
    domain.fftNatural poly (domain.base.lowerIndex h i) =
      domain.toCosetNTTSpec.transform poly (domain.base.lowerIndex h i) := by
  simpa using congrFun (domain.fftNatural_eq_transform poly) (domain.base.lowerIndex h i)

theorem fftNatural_upperIndex_eq_transform (domain : CosetRadix2Domain F)
    (h : 0 < domain.base.logSize) (poly : Polynomial F) (i : Fin domain.base.halfSize) :
    domain.fftNatural poly (domain.base.upperIndex h i) =
      domain.toCosetNTTSpec.transform poly (domain.base.upperIndex h i) := by
  simpa using congrFun (domain.fftNatural_eq_transform poly) (domain.base.upperIndex h i)

theorem fftNatural_lowerIndex_eq_evenOdd (domain : CosetRadix2Domain F)
    (h : 0 < domain.base.logSize) (poly : Polynomial F) (i : Fin domain.base.halfSize) :
    domain.fftNatural poly (domain.base.lowerIndex h i) =
      (domain.halfSquareDomain h).fftNatural (PolynomialParity.evenPart poly) i +
      domain.point (domain.base.lowerIndex h i) *
        (domain.halfSquareDomain h).fftNatural (PolynomialParity.oddPart poly) i := by
  rw [domain.fftNatural_eq_transform, domain.transform_lowerIndex_eq_evenOdd]
  rw [(domain.halfSquareDomain h).fftNatural_eq_transform (PolynomialParity.evenPart poly)]
  rw [(domain.halfSquareDomain h).fftNatural_eq_transform (PolynomialParity.oddPart poly)]

theorem fftNatural_upperIndex_eq_even_sub_twiddled_odd (domain : CosetRadix2Domain F)
    (h : 0 < domain.base.logSize) (poly : Polynomial F) (i : Fin domain.base.halfSize) :
    domain.fftNatural poly (domain.base.upperIndex h i) =
      (domain.halfSquareDomain h).fftNatural (PolynomialParity.evenPart poly) i -
      domain.point (domain.base.lowerIndex h i) *
        (domain.halfSquareDomain h).fftNatural (PolynomialParity.oddPart poly) i := by
  rw [domain.fftNatural_eq_transform, domain.transform_upperIndex_eq_even_sub_twiddled_odd]
  rw [(domain.halfSquareDomain h).fftNatural_eq_transform (PolynomialParity.evenPart poly)]
  rw [(domain.halfSquareDomain h).fftNatural_eq_transform (PolynomialParity.oddPart poly)]

end CosetRadix2Domain

end Zklib.Core
