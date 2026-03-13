import Zklib.Core.NTT.Radix2.CosetCoefficientSplit
import Zklib.Core.NTT.Radix2.Natural

namespace Zklib.Core

namespace CosetRadix2Domain

variable {F : Type*} [Field F]

/--
A coefficient-recursive radix-2 FFT on a coset domain, producing values in
natural order.

The recursion descends on the even/odd coefficient split, so the child domain
uses the squared shift.
-/
noncomputable def fftNaturalAux :
    (k : Nat) ->
    (domain : CosetRadix2Domain F) ->
    domain.base.logSize = k ->
    Polynomial F ->
    Fin domain.base.size -> F
  | 0, domain, hk, poly =>
      domain.toCosetNTTSpec.transform poly
  | Nat.succ k, domain, hk, poly =>
      let hpos : 0 < domain.base.logSize := by
        simp [hk]
      let half := domain.halfSquareDomain hpos
      let hkHalf : half.base.logSize = k := by
        simp [half, CosetRadix2Domain.halfSquareDomain, Radix2Domain.halfDomain, hk]
      let evenVals := fftNaturalAux k half hkHalf (PolynomialParity.evenPart poly)
      let oddVals := fftNaturalAux k half hkHalf (PolynomialParity.oddPart poly)
      let stage := Radix2.butterflyValues
        (fun i => domain.point (domain.base.lowerIndex hpos i))
        evenVals oddVals
      domain.base.combineNaturalOrder hpos stage.1 stage.2

/--
The natural-order coefficient-recursive coset FFT on a concrete coset radix-2
domain.
-/
noncomputable def fftNatural (domain : CosetRadix2Domain F) (poly : Polynomial F) :
    Fin domain.base.size -> F :=
  fftNaturalAux domain.base.logSize domain rfl poly

theorem fftNaturalAux_zero (domain : CosetRadix2Domain F) (hk : domain.base.logSize = 0)
    (poly : Polynomial F) :
    fftNaturalAux 0 domain hk poly = domain.toCosetNTTSpec.transform poly := by
  rfl

theorem fftNaturalAux_succ (k : Nat) (domain : CosetRadix2Domain F)
    (hk : domain.base.logSize = k + 1) (poly : Polynomial F) :
    fftNaturalAux (k + 1) domain hk poly =
      let hpos : 0 < domain.base.logSize := by simp [hk]
      let half := domain.halfSquareDomain hpos
      let hkHalf : half.base.logSize = k := by
        simp [half, CosetRadix2Domain.halfSquareDomain, Radix2Domain.halfDomain, hk]
      let evenVals := fftNaturalAux k half hkHalf (PolynomialParity.evenPart poly)
      let oddVals := fftNaturalAux k half hkHalf (PolynomialParity.oddPart poly)
      let stage := Radix2.butterflyValues
        (fun i => domain.point (domain.base.lowerIndex hpos i))
        evenVals oddVals
      domain.base.combineNaturalOrder hpos stage.1 stage.2 := by
  rfl

theorem fftNaturalAux_eq_transform :
    (k : Nat) ->
    (domain : CosetRadix2Domain F) ->
    (hk : domain.base.logSize = k) ->
    (poly : Polynomial F) ->
    fftNaturalAux k domain hk poly = domain.toCosetNTTSpec.transform poly
  | 0, domain, hk, poly => by
      rfl
  | k + 1, domain, hk, poly => by
      let hpos : 0 < domain.base.logSize := by
        simp [hk]
      let half := domain.halfSquareDomain hpos
      have hkHalf : half.base.logSize = k := by
        simp [half, CosetRadix2Domain.halfSquareDomain, Radix2Domain.halfDomain, hk]
      let stage :=
        Radix2.butterflyValues
          (fun i => domain.point (domain.base.lowerIndex hpos i))
          (fftNaturalAux k half hkHalf (PolynomialParity.evenPart poly))
          (fftNaturalAux k half hkHalf (PolynomialParity.oddPart poly))
      apply domain.base.naturalOrder_ext hpos
      calc
        domain.base.naturalOrderPair hpos (fftNaturalAux (k + 1) domain hk poly)
            = stage := by
                rw [fftNaturalAux_succ k domain hk poly]
                simpa [stage, hpos, half, hkHalf] using
                  (domain.base.naturalOrderPair_combineNaturalOrder hpos stage.1 stage.2)
        _ = Radix2.butterflyValues
              (fun i => domain.point (domain.base.lowerIndex hpos i))
              ((domain.halfSquareDomain hpos).toCosetNTTSpec.transform
                (PolynomialParity.evenPart poly))
              ((domain.halfSquareDomain hpos).toCosetNTTSpec.transform
                (PolynomialParity.oddPart poly)) := by
                dsimp [stage]
                rw [fftNaturalAux_eq_transform k half hkHalf (PolynomialParity.evenPart poly),
                  fftNaturalAux_eq_transform k half hkHalf (PolynomialParity.oddPart poly)]
        _ = domain.base.naturalOrderPair hpos (domain.toCosetNTTSpec.transform poly) := by
              exact (domain.transform_naturalOrder_eq_butterflyValues hpos poly).symm

theorem fftNatural_eq_transform (domain : CosetRadix2Domain F) (poly : Polynomial F) :
    domain.fftNatural poly = domain.toCosetNTTSpec.transform poly := by
  simpa [fftNatural] using fftNaturalAux_eq_transform domain.base.logSize domain rfl poly

end CosetRadix2Domain

end Zklib.Core
