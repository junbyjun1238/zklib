import Zklib.Core.NTT.Radix2.Flatten

namespace Zklib.Core

namespace Radix2Domain

variable {F : Type*} [Field F]

/--
A recursive radix-2 FFT whose output is flattened in parity order.

At each recursive step we descend to the half-domain, first on the original
polynomial and then on its generator twist. Flattening this recursion yields
the usual bit-reversed output order.
-/
noncomputable def fftAux :
    (k : Nat) ->
    (domain : Radix2Domain F) ->
    domain.logSize = k ->
    Polynomial F ->
    List F
  | 0, domain, hk, poly =>
      [domain.toNTTSpec.transform poly (Fin.mk 0 domain.size_pos)]
  | Nat.succ k, domain, hk, poly =>
      let half := domain.succHalf hk
      let hkHalf : half.logSize = k := by
        simp [half]
      fftAux k half hkHalf poly ++
        fftAux k half hkHalf (domain.twistPolynomial poly)

/--
The recursive radix-2 FFT on a concrete domain.
-/
noncomputable def fft (domain : Radix2Domain F) (poly : Polynomial F) : List F :=
  fftAux domain.logSize domain rfl poly

theorem fftAux_zero (domain : Radix2Domain F) (hk : domain.logSize = 0)
    (poly : Polynomial F) :
    fftAux 0 domain hk poly =
      [domain.toNTTSpec.transform poly (Fin.mk 0 domain.size_pos)] := by
  rfl

theorem fftAux_succ (k : Nat) (domain : Radix2Domain F)
    (hk : domain.logSize = k + 1) (poly : Polynomial F) :
    fftAux (k + 1) domain hk poly =
      fftAux k (domain.succHalf hk)
        (by simp) poly ++
      fftAux k (domain.succHalf hk)
        (by simp) (domain.twistPolynomial poly) := by
  rfl

theorem length_fftAux :
    (k : Nat) ->
    (domain : Radix2Domain F) ->
    (hk : domain.logSize = k) ->
    (poly : Polynomial F) ->
    (fftAux k domain hk poly).length = domain.size
  | 0, domain, hk, poly => by
      have hsize : domain.size = 1 := by
        simpa [hk] using domain.size_eq_pow
      simp [fftAux, hsize]
  | k + 1, domain, hk, poly => by
      let hpos : 0 < domain.logSize := by
        simp [hk]
      let half := domain.succHalf hk
      have hkHalf : half.logSize = k := by
        simp [half]
      calc
        (fftAux (k + 1) domain hk poly).length
            = (fftAux k half hkHalf poly).length +
              (fftAux k half hkHalf (domain.twistPolynomial poly)).length := by
                simp [fftAux, half]
        _ = half.size + half.size := by
              rw [length_fftAux k half hkHalf poly,
                length_fftAux k half hkHalf (domain.twistPolynomial poly)]
        _ = domain.size := by
              simpa [half] using (domain.size_eq_halfSize_add_halfSize hpos).symm

theorem length_fft (domain : Radix2Domain F) (poly : Polynomial F) :
    (domain.fft poly).length = domain.size := by
  simpa [fft] using length_fftAux domain.logSize domain rfl poly

end Radix2Domain

end Zklib.Core
