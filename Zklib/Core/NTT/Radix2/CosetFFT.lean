import Zklib.Core.NTT.Radix2.CosetCorrectness

namespace Zklib.Core

namespace CosetRadix2Domain

variable {F : Type*} [Field F]

/--
A parity-recursive radix-2 FFT over a coset domain.

Unlike the cyclic case, the odd branch is represented by a shifted child coset
domain, so the recursion keeps the same polynomial and descends into distinct
even/odd coset domains.
-/
noncomputable def fftAux :
    (k : Nat) ->
    (domain : CosetRadix2Domain F) ->
    domain.base.logSize = k ->
    Polynomial F ->
    List F
  | 0, domain, hk, poly =>
      [domain.toCosetNTTSpec.transform poly (Fin.mk 0 domain.base.size_pos)]
  | Nat.succ k, domain, hk, poly =>
      let hpos : 0 < domain.base.logSize := by simp [hk]
      let evenDom := domain.halfEvenDomain hpos
      let oddDom := domain.halfOddDomain hpos
      let hkHalf : evenDom.base.logSize = k := by
        simp [evenDom, CosetRadix2Domain.halfEvenDomain, Radix2Domain.halfDomain, hk]
      let hkHalfOdd : oddDom.base.logSize = k := by
        simp [oddDom, CosetRadix2Domain.halfOddDomain, Radix2Domain.halfDomain, hk]
      fftAux k evenDom hkHalf poly ++
        fftAux k oddDom hkHalfOdd poly

/--
The recursive radix-2 FFT on a concrete coset domain.
-/
noncomputable def fft (domain : CosetRadix2Domain F) (poly : Polynomial F) : List F :=
  fftAux domain.base.logSize domain rfl poly

theorem fftAux_zero (domain : CosetRadix2Domain F) (hk : domain.base.logSize = 0)
    (poly : Polynomial F) :
    fftAux 0 domain hk poly =
      [domain.toCosetNTTSpec.transform poly (Fin.mk 0 domain.base.size_pos)] := by
  rfl

theorem fftAux_succ (k : Nat) (domain : CosetRadix2Domain F)
    (hk : domain.base.logSize = k + 1) (poly : Polynomial F) :
    fftAux (k + 1) domain hk poly =
      fftAux k (domain.halfEvenDomain (by simp [hk]))
        (by simp [CosetRadix2Domain.halfEvenDomain, Radix2Domain.halfDomain, hk]) poly ++
      fftAux k (domain.halfOddDomain (by simp [hk]))
        (by simp [CosetRadix2Domain.halfOddDomain, Radix2Domain.halfDomain, hk]) poly := by
  rfl

theorem length_fftAux :
    (k : Nat) ->
    (domain : CosetRadix2Domain F) ->
    (hk : domain.base.logSize = k) ->
    (poly : Polynomial F) ->
    (fftAux k domain hk poly).length = domain.base.size
  | 0, domain, hk, poly => by
      have hsize : domain.base.size = 1 := by
        simpa [hk] using domain.base.size_eq_pow
      simp [fftAux, hsize]
  | k + 1, domain, hk, poly => by
      let hpos : 0 < domain.base.logSize := by simp [hk]
      let evenDom := domain.halfEvenDomain hpos
      let oddDom := domain.halfOddDomain hpos
      have hkEven : evenDom.base.logSize = k := by
        simp [evenDom, CosetRadix2Domain.halfEvenDomain, Radix2Domain.halfDomain, hk]
      have hkOdd : oddDom.base.logSize = k := by
        simp [oddDom, CosetRadix2Domain.halfOddDomain, Radix2Domain.halfDomain, hk]
      calc
        (fftAux (k + 1) domain hk poly).length
            = (fftAux k evenDom hkEven poly).length +
              (fftAux k oddDom hkOdd poly).length := by
                simp [fftAux, evenDom, oddDom]
        _ = evenDom.base.size + oddDom.base.size := by
              rw [length_fftAux k evenDom hkEven poly, length_fftAux k oddDom hkOdd poly]
        _ = domain.base.size := by
              have hevenSize : evenDom.base.size = domain.base.halfSize := by
                rfl
              have hoddSize : oddDom.base.size = domain.base.halfSize := by
                rfl
              rw [hevenSize, hoddSize, domain.base.size_eq_halfSize_add_halfSize hpos]

theorem length_fft (domain : CosetRadix2Domain F) (poly : Polynomial F) :
    (domain.fft poly).length = domain.base.size := by
  simpa [fft] using length_fftAux domain.base.logSize domain rfl poly

end CosetRadix2Domain

end Zklib.Core
