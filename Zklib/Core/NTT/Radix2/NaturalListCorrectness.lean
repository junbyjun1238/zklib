import Zklib.Core.NTT.Radix2.NaturalList

namespace Zklib.Core

namespace Radix2Domain

variable {F : Type*} [Field F]

theorem fftNaturalListAux_eq_ofFn :
    (k : Nat) ->
    (domain : Radix2Domain F) ->
    (hk : domain.logSize = k) ->
    (poly : Polynomial F) ->
    fftNaturalListAux k domain hk poly = List.ofFn (fftNaturalAux k domain hk poly)
  | 0, domain, hk, poly => by
      have hsize : domain.size = 1 := by
        simpa [hk] using domain.size_eq_pow
      calc
        fftNaturalListAux 0 domain hk poly
            = [domain.toNTTSpec.transform poly (Fin.mk 0 domain.size_pos)] := by
                rfl
        _ = [domain.toNTTSpec.transform poly (Fin.cast hsize.symm 0)] := by
              have hidx :
                  (Fin.mk 0 domain.size_pos : Fin domain.size) = Fin.cast hsize.symm 0 := by
                ext
                simp
              simpa using congrArg (domain.toNTTSpec.transform poly) hidx
        _ = List.ofFn (fun i : Fin 1 => domain.toNTTSpec.transform poly (Fin.cast hsize.symm i)) := by
              simp
        _ = List.ofFn (fftNaturalAux 0 domain hk poly) := by
              simpa [fftNaturalAux] using
                (List.ofFn_congr (h := hsize) (f := domain.toNTTSpec.transform poly)).symm
  | k + 1, domain, hk, poly => by
      let hpos : 0 < domain.logSize := by
        simp [hk]
      let half := domain.succHalf hk
      have hkHalf : half.logSize = k := by
        simp [half]
      have heven :
          ↑(fftNaturalListAuxData k half hkHalf (PolynomialParity.evenPart poly)) =
            List.ofFn (fftNaturalAux k half hkHalf (PolynomialParity.evenPart poly)) := by
        simpa [fftNaturalListAux] using
          (fftNaturalListAux_eq_ofFn k half hkHalf (PolynomialParity.evenPart poly))
      have hodd :
          ↑(fftNaturalListAuxData k half hkHalf (PolynomialParity.oddPart poly)) =
            List.ofFn (fftNaturalAux k half hkHalf (PolynomialParity.oddPart poly)) := by
        simpa [fftNaturalListAux] using
          (fftNaturalListAux_eq_ofFn k half hkHalf (PolynomialParity.oddPart poly))
      rw [fftNaturalAux_succ k domain hk poly]
      have hstage :=
        domain.butterflyStageList_eq_ofFn hpos
          (fftNaturalAux k half hkHalf (PolynomialParity.evenPart poly))
          (fftNaturalAux k half hkHalf (PolynomialParity.oddPart poly))
      simpa [fftNaturalListAux, fftNaturalListAuxData, hpos, half, hkHalf, heven, hodd] using hstage

theorem fftNaturalList_eq_ofFn (domain : Radix2Domain F) (poly : Polynomial F) :
    domain.fftNaturalList poly = List.ofFn (domain.fftNatural poly) := by
  simpa [fftNaturalList, fftNatural] using
    fftNaturalListAux_eq_ofFn domain.logSize domain rfl poly

theorem fftNaturalList_eq_listOfTable (domain : Radix2Domain F) (poly : Polynomial F) :
    domain.fftNaturalList poly = Radix2Representation.listOfTable (domain.fftNatural poly) := by
  simpa [Radix2Representation.listOfTable] using domain.fftNaturalList_eq_ofFn poly

theorem fftNaturalList_eq_ofFn_transform (domain : Radix2Domain F) (poly : Polynomial F) :
    domain.fftNaturalList poly = List.ofFn (domain.toNTTSpec.transform poly) := by
  calc
    domain.fftNaturalList poly = List.ofFn (domain.fftNatural poly) := fftNaturalList_eq_ofFn domain poly
    _ = List.ofFn (domain.toNTTSpec.transform poly) := by
          rw [domain.fftNatural_eq_transform poly]
          rfl

end Radix2Domain

end Zklib.Core
