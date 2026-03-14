import Zklib.Core.NTT.Radix2.CosetFFT
import Zklib.Core.NTT.Radix2.CosetFlatten

namespace Zklib.Core

namespace CosetRadix2Domain

variable {F : Type*} [Field F]

theorem fftAux_eq_parityTreeAux_flatten :
    (k : Nat) ->
    (domain : CosetRadix2Domain F) ->
    (hk : domain.base.logSize = k) ->
    (poly : Polynomial F) ->
    fftAux k domain hk poly = (parityTreeAux k domain hk poly).flatten
  | 0, domain, hk, poly => by
      rfl
  | k + 1, domain, hk, poly => by
      let evenDom := domain.succHalfEven hk
      let oddDom := domain.succHalfOdd hk
      have hkEven : evenDom.base.logSize = k := by
        simp [evenDom]
      have hkOdd : oddDom.base.logSize = k := by
        simp [oddDom]
      have htree :
          (parityTreeAux (k + 1) domain hk poly).flatten =
            (parityTreeAux k evenDom hkEven poly).flatten ++
            (parityTreeAux k oddDom hkOdd poly).flatten := by
        simpa [evenDom, oddDom, hkEven, hkOdd, Radix2.FFTTree.flatten] using
          congrArg Radix2.FFTTree.flatten (parityTreeAux_succ k domain hk poly)
      calc
        fftAux (k + 1) domain hk poly
            = fftAux k evenDom hkEven poly ++
              fftAux k oddDom hkOdd poly := by
                simpa [evenDom, oddDom, hkEven, hkOdd] using fftAux_succ k domain hk poly
        _ = (parityTreeAux k evenDom hkEven poly).flatten ++
              (parityTreeAux k oddDom hkOdd poly).flatten := by
                rw [fftAux_eq_parityTreeAux_flatten k evenDom hkEven poly,
                  fftAux_eq_parityTreeAux_flatten k oddDom hkOdd poly]
        _ = (parityTreeAux (k + 1) domain hk poly).flatten := by
              exact htree.symm

theorem fft_eq_valuesInParityOrder (domain : CosetRadix2Domain F) (poly : Polynomial F) :
    domain.fft poly = domain.valuesInParityOrder poly := by
  simpa [fft, valuesInParityOrder, parityTree] using
    fftAux_eq_parityTreeAux_flatten domain.base.logSize domain rfl poly

theorem fft_eq_map_transform_bitRevOrder (domain : CosetRadix2Domain F)
    (poly : Polynomial F) :
    domain.fft poly =
      domain.bitRevOrder.map (fun i => domain.toCosetNTTSpec.transform poly i) := by
  rw [fft_eq_valuesInParityOrder]
  exact valuesInParityOrder_eq_map_transform_bitRevOrder domain poly

theorem fft_eq_map_transform_bitRevOrderFn (domain : CosetRadix2Domain F)
    (poly : Polynomial F) :
    domain.fft poly =
      domain.bitRevOrderFn.map (fun i => domain.toCosetNTTSpec.transform poly i) := by
  rw [fft_eq_valuesInParityOrder]
  exact valuesInParityOrder_eq_map_transform_bitRevOrderFn domain poly

end CosetRadix2Domain

end Zklib.Core
