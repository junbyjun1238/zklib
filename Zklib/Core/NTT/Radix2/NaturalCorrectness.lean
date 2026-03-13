import Zklib.Core.NTT.Radix2.Natural

namespace Zklib.Core

namespace Radix2Domain

variable {F : Type*} [Field F]

theorem fftNatural_lowerIndex_eq_transform (domain : Radix2Domain F)
    (h : 0 < domain.logSize) (poly : Polynomial F) (i : Fin domain.halfSize) :
    domain.fftNatural poly (domain.lowerIndex h i) =
      domain.toNTTSpec.transform poly (domain.lowerIndex h i) := by
  simpa using congrFun (domain.fftNatural_eq_transform poly) (domain.lowerIndex h i)

theorem fftNatural_upperIndex_eq_transform (domain : Radix2Domain F)
    (h : 0 < domain.logSize) (poly : Polynomial F) (i : Fin domain.halfSize) :
    domain.fftNatural poly (domain.upperIndex h i) =
      domain.toNTTSpec.transform poly (domain.upperIndex h i) := by
  simpa using congrFun (domain.fftNatural_eq_transform poly) (domain.upperIndex h i)

theorem fftNatural_lowerIndex_eq_evenOdd (domain : Radix2Domain F)
    (h : 0 < domain.logSize) (poly : Polynomial F) (i : Fin domain.halfSize) :
    domain.fftNatural poly (domain.lowerIndex h i) =
      (domain.halfDomain h).fftNatural (PolynomialParity.evenPart poly) i +
      domain.point (domain.lowerIndex h i) *
        (domain.halfDomain h).fftNatural (PolynomialParity.oddPart poly) i := by
  rw [fftNatural_eq_transform, transform_lowerIndex_eq_evenOdd]
  rw [(domain.halfDomain h).fftNatural_eq_transform (PolynomialParity.evenPart poly)]
  rw [(domain.halfDomain h).fftNatural_eq_transform (PolynomialParity.oddPart poly)]

theorem fftNatural_upperIndex_eq_even_sub_twiddled_odd (domain : Radix2Domain F)
    (h : 0 < domain.logSize) (poly : Polynomial F) (i : Fin domain.halfSize) :
    domain.fftNatural poly (domain.upperIndex h i) =
      (domain.halfDomain h).fftNatural (PolynomialParity.evenPart poly) i -
      domain.point (domain.lowerIndex h i) *
        (domain.halfDomain h).fftNatural (PolynomialParity.oddPart poly) i := by
  rw [fftNatural_eq_transform, transform_upperIndex_eq_even_sub_twiddled_odd]
  rw [(domain.halfDomain h).fftNatural_eq_transform (PolynomialParity.evenPart poly)]
  rw [(domain.halfDomain h).fftNatural_eq_transform (PolynomialParity.oddPart poly)]

end Radix2Domain

end Zklib.Core
