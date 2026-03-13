import Zklib.Core.NTT.Radix2.CosetNaturalList

namespace Zklib.Core

namespace CosetRadix2Domain

variable {F : Type*} [Field F]

theorem fftNaturalListAux_eq_ofFn :
    (k : Nat) ->
    (domain : CosetRadix2Domain F) ->
    (hk : domain.base.logSize = k) ->
    (poly : Polynomial F) ->
    fftNaturalListAux k domain hk poly = List.ofFn (fftNaturalAux k domain hk poly)
  | 0, domain, hk, poly => by
      have hsize : domain.base.size = 1 := by
        simpa [hk] using domain.base.size_eq_pow
      calc
        fftNaturalListAux 0 domain hk poly
            = [domain.toCosetNTTSpec.transform poly (Fin.mk 0 domain.base.size_pos)] := by
                rfl
        _ = [domain.toCosetNTTSpec.transform poly (Fin.cast hsize.symm 0)] := by
              have hidx :
                  (Fin.mk 0 domain.base.size_pos : Fin domain.base.size) = Fin.cast hsize.symm 0 := by
                ext
                simp
              simpa using congrArg (domain.toCosetNTTSpec.transform poly) hidx
        _ = List.ofFn (fun i : Fin 1 => domain.toCosetNTTSpec.transform poly (Fin.cast hsize.symm i)) := by
              simp
        _ = List.ofFn (fftNaturalAux 0 domain hk poly) := by
              simpa [fftNaturalAux] using
                (List.ofFn_congr (h := hsize) (f := domain.toCosetNTTSpec.transform poly)).symm
  | k + 1, domain, hk, poly => by
      let hpos : 0 < domain.base.logSize := by
        simp [hk]
      let half := domain.halfSquareDomain hpos
      have hkHalf : half.base.logSize = k := by
        simp [half, CosetRadix2Domain.halfSquareDomain, Radix2Domain.halfDomain, hk]
      have heven :
          (fftNaturalListAuxData k half hkHalf (PolynomialParity.evenPart poly)).1 =
            List.ofFn (fftNaturalAux k half hkHalf (PolynomialParity.evenPart poly)) := by
        simpa [fftNaturalListAux] using
          (fftNaturalListAux_eq_ofFn k half hkHalf (PolynomialParity.evenPart poly))
      have hodd :
          (fftNaturalListAuxData k half hkHalf (PolynomialParity.oddPart poly)).1 =
            List.ofFn (fftNaturalAux k half hkHalf (PolynomialParity.oddPart poly)) := by
        simpa [fftNaturalListAux] using
          (fftNaturalListAux_eq_ofFn k half hkHalf (PolynomialParity.oddPart poly))
      rw [fftNaturalAux_succ k domain hk poly]
      have hstage :=
        domain.butterflyStageList_eq_ofFn hpos
          (fftNaturalAux k half hkHalf (PolynomialParity.evenPart poly))
          (fftNaturalAux k half hkHalf (PolynomialParity.oddPart poly))
      simpa [fftNaturalListAux, fftNaturalListAuxData, hpos, half, hkHalf, heven, hodd] using hstage

theorem fftNaturalList_eq_ofFn (domain : CosetRadix2Domain F) (poly : Polynomial F) :
    domain.fftNaturalList poly = List.ofFn (domain.fftNatural poly) := by
  simpa [fftNaturalList, fftNatural] using
    fftNaturalListAux_eq_ofFn domain.base.logSize domain rfl poly

theorem fftNaturalList_eq_ofFn_transform (domain : CosetRadix2Domain F) (poly : Polynomial F) :
    domain.fftNaturalList poly = List.ofFn (domain.toCosetNTTSpec.transform poly) := by
  calc
    domain.fftNaturalList poly = List.ofFn (domain.fftNatural poly) := fftNaturalList_eq_ofFn domain poly
    _ = List.ofFn (domain.toCosetNTTSpec.transform poly) := by
          rw [domain.fftNatural_eq_transform poly]
          rfl

end CosetRadix2Domain

end Zklib.Core
