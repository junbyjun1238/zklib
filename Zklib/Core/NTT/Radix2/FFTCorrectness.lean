import Zklib.Core.NTT.Radix2.FFT
import Zklib.Core.NTT.Radix2.BitReversal

namespace Zklib.Core

namespace Radix2Domain

variable {F : Type*} [Field F]

theorem fftAux_eq_parityTreeAux_flatten :
    (k : Nat) ->
    (domain : Radix2Domain F) ->
    (hk : domain.logSize = k) ->
    (poly : Polynomial F) ->
    fftAux k domain hk poly = (parityTreeAux k domain hk poly).flatten
  | 0, domain, hk, poly => by
      rfl
  | k + 1, domain, hk, poly => by
      let half := domain.succHalf hk
      have hkHalf : half.logSize = k := by
        simp [half]
      have htree :
          (parityTreeAux (k + 1) domain hk poly).flatten =
            (parityTreeAux k half hkHalf poly).flatten ++
            (parityTreeAux k half hkHalf (domain.twistPolynomial poly)).flatten := by
        simpa [half, hkHalf, Radix2.FFTTree.flatten] using
          congrArg Radix2.FFTTree.flatten (parityTreeAux_succ k domain hk poly)
      calc
        fftAux (k + 1) domain hk poly
            = fftAux k half hkHalf poly ++
              fftAux k half hkHalf (domain.twistPolynomial poly) := by
                simpa [half, hkHalf] using fftAux_succ k domain hk poly
        _ = (parityTreeAux k half hkHalf poly).flatten ++
              (parityTreeAux k half hkHalf (domain.twistPolynomial poly)).flatten := by
                rw [fftAux_eq_parityTreeAux_flatten k half hkHalf poly,
                  fftAux_eq_parityTreeAux_flatten k half hkHalf (domain.twistPolynomial poly)]
        _ = (parityTreeAux (k + 1) domain hk poly).flatten := by
              exact htree.symm

theorem fft_eq_valuesInParityOrder (domain : Radix2Domain F) (poly : Polynomial F) :
    domain.fft poly = domain.valuesInParityOrder poly := by
  simpa [fft, valuesInParityOrder, parityTree] using
    fftAux_eq_parityTreeAux_flatten domain.logSize domain rfl poly

theorem fft_eq_map_transform_bitRevOrder (domain : Radix2Domain F)
    (poly : Polynomial F) :
    domain.fft poly =
      domain.bitRevOrder.map (fun i => domain.toNTTSpec.transform poly i) := by
  rw [fft_eq_valuesInParityOrder]
  exact valuesInParityOrder_eq_map_transform_bitRevOrder domain poly

theorem fft_eq_map_transform_bitRevOrderFn (domain : Radix2Domain F)
    (poly : Polynomial F) :
    domain.fft poly =
      domain.bitRevOrderFn.map (fun i => domain.toNTTSpec.transform poly i) := by
  rw [fft_eq_valuesInParityOrder]
  exact valuesInParityOrder_eq_map_transform_bitRevOrderFn domain poly

end Radix2Domain

end Zklib.Core
