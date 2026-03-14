import Zklib.Core.NTT.Radix2.CosetNaturalArray
import Zklib.Core.NTT.Radix2.CosetNaturalListCorrectness

namespace Zklib.Core

namespace CosetRadix2Domain

variable {F : Type*} [Field F]

theorem fftNaturalArrayAux_toList_eq :
    (k : Nat) ->
    (domain : CosetRadix2Domain F) ->
    (hk : domain.base.logSize = k) ->
    (poly : Polynomial F) ->
    (fftNaturalArrayAux k domain hk poly).toList = fftNaturalListAux k domain hk poly
  | 0, domain, hk, poly => by
      rfl
  | k + 1, domain, hk, poly => by
      let hpos : 0 < domain.base.logSize := by
        simp [hk]
      let half := domain.succHalfSquare hk
      have hkHalf : half.base.logSize = k := by
        simp [half]
      let evenData := fftNaturalArrayAuxData k half hkHalf (PolynomialParity.evenPart poly)
      let oddData := fftNaturalArrayAuxData k half hkHalf (PolynomialParity.oddPart poly)
      have heven :
          evenData.1.toList =
            fftNaturalListAux k half hkHalf (PolynomialParity.evenPart poly) := by
        simpa [fftNaturalArrayAux] using
          (fftNaturalArrayAux_toList_eq k half hkHalf (PolynomialParity.evenPart poly))
      have hodd :
          oddData.1.toList =
            fftNaturalListAux k half hkHalf (PolynomialParity.oddPart poly) := by
        simpa [fftNaturalArrayAux] using
          (fftNaturalArrayAux_toList_eq k half hkHalf (PolynomialParity.oddPart poly))
      calc
        (fftNaturalArrayAux (k + 1) domain hk poly).toList
            = (domain.butterflyStageArray hpos evenData.1 oddData.1 evenData.2 oddData.2).toList := by
                rfl
        _ = domain.butterflyStageList hpos evenData.1.toList oddData.1.toList
              (by rw [Array.length_toList]; exact evenData.2)
              (by rw [Array.length_toList]; exact oddData.2) := by
                exact
                  (domain.toList_butterflyStageArray hpos evenData.1 oddData.1 evenData.2 oddData.2)
        _ = domain.butterflyStageList hpos
              (fftNaturalListAux k half hkHalf (PolynomialParity.evenPart poly))
              (fftNaturalListAux k half hkHalf (PolynomialParity.oddPart poly))
              (by simpa using length_fftNaturalListAux k half hkHalf (PolynomialParity.evenPart poly))
              (by simpa using length_fftNaturalListAux k half hkHalf (PolynomialParity.oddPart poly)) := by
                exact domain.butterflyStageList_congr hpos heven hodd
        _ = fftNaturalListAux (k + 1) domain hk poly := by
              rfl

theorem fftNaturalArray_toList_eq (domain : CosetRadix2Domain F) (poly : Polynomial F) :
    (domain.fftNaturalArray poly).toList = domain.fftNaturalList poly := by
  simpa [fftNaturalArray, fftNaturalList] using
    fftNaturalArrayAux_toList_eq domain.base.logSize domain rfl poly

theorem fftNaturalArray_eq_toArray (domain : CosetRadix2Domain F) (poly : Polynomial F) :
    domain.fftNaturalArray poly = (domain.fftNaturalList poly).toArray := by
  apply Array.ext'
  simpa using domain.fftNaturalArray_toList_eq poly

theorem fftNaturalArray_eq_arrayOfTable (domain : CosetRadix2Domain F) (poly : Polynomial F) :
    domain.fftNaturalArray poly = Radix2Representation.arrayOfTable (domain.fftNatural poly) := by
  apply Array.ext'
  rw [Radix2Representation.arrayOfTable_toList]
  rw [fftNaturalArray_toList_eq, domain.fftNaturalList_eq_listOfTable]

theorem fftNaturalArray_toList_eq_ofFn (domain : CosetRadix2Domain F) (poly : Polynomial F) :
    (domain.fftNaturalArray poly).toList = List.ofFn (domain.fftNatural poly) := by
  rw [fftNaturalArray_toList_eq, domain.fftNaturalList_eq_ofFn poly]

theorem fftNaturalArray_toList_eq_ofFn_transform
    (domain : CosetRadix2Domain F) (poly : Polynomial F) :
    (domain.fftNaturalArray poly).toList = List.ofFn (domain.toCosetNTTSpec.transform poly) := by
  rw [fftNaturalArray_toList_eq, domain.fftNaturalList_eq_ofFn_transform poly]

end CosetRadix2Domain

end Zklib.Core
