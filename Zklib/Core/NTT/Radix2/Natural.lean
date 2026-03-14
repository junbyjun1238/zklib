import Zklib.Core.NTT.Radix2.CoefficientSplit

namespace Zklib.Core

namespace Radix2Domain

variable {F : Type*} [Field F]

/--
Combine lower-half and upper-half tables into a full natural-order table.
-/
def combineNaturalOrder (domain : Radix2Domain F) (h : 0 < domain.logSize)
    (lower upper : Fin domain.halfSize -> F) : Fin domain.size -> F :=
  fun j =>
    Fin.addCases lower upper
      (Fin.cast (domain.size_eq_halfSize_add_halfSize h) j)

theorem combineNaturalOrder_lowerIndex (domain : Radix2Domain F) (h : 0 < domain.logSize)
    (lower upper : Fin domain.halfSize -> F) (i : Fin domain.halfSize) :
    domain.combineNaturalOrder h lower upper (domain.lowerIndex h i) = lower i := by
  change Fin.addCases lower upper (Fin.castAdd domain.halfSize i) = lower i
  exact Fin.addCases_left i

theorem combineNaturalOrder_upperIndex (domain : Radix2Domain F) (h : 0 < domain.logSize)
    (lower upper : Fin domain.halfSize -> F) (i : Fin domain.halfSize) :
    domain.combineNaturalOrder h lower upper (domain.upperIndex h i) = upper i := by
  change Fin.addCases lower upper (Fin.natAdd domain.halfSize i) = upper i
  exact Fin.addCases_right i

/--
The lower/upper natural-order view of a full domain table.
-/
def naturalOrderPair (domain : Radix2Domain F) (h : 0 < domain.logSize)
    (values : Fin domain.size -> F) : (Fin domain.halfSize -> F) × (Fin domain.halfSize -> F) :=
  (fun i => values (domain.lowerIndex h i), fun i => values (domain.upperIndex h i))

theorem naturalOrderPair_combineNaturalOrder (domain : Radix2Domain F) (h : 0 < domain.logSize)
    (lower upper : Fin domain.halfSize -> F) :
    domain.naturalOrderPair h (domain.combineNaturalOrder h lower upper) = (lower, upper) := by
  ext i <;> simp [naturalOrderPair, combineNaturalOrder_lowerIndex, combineNaturalOrder_upperIndex]

theorem naturalOrder_ext (domain : Radix2Domain F) (h : 0 < domain.logSize)
    {f g : Fin domain.size -> F}
    (hpair : domain.naturalOrderPair h f = domain.naturalOrderPair h g) :
    f = g := by
  funext j
  let j' : Fin (domain.halfSize + domain.halfSize) :=
    Fin.cast (domain.size_eq_halfSize_add_halfSize h) j
  have hj : j = Fin.cast (domain.size_eq_halfSize_add_halfSize h).symm j' := by
    simp [j']
  rw [hj]
  refine Fin.addCases ?_ ?_ j'
  · intro i
    exact congrFun (congrArg Prod.fst hpair) i
  · intro i
    exact congrFun (congrArg Prod.snd hpair) i

theorem combineNaturalOrder_naturalOrderPair (domain : Radix2Domain F) (h : 0 < domain.logSize)
    (values : Fin domain.size -> F) :
    domain.combineNaturalOrder h (domain.naturalOrderPair h values).1
      (domain.naturalOrderPair h values).2 = values := by
  apply domain.naturalOrder_ext h
  simpa using
    (domain.naturalOrderPair_combineNaturalOrder h
      (domain.naturalOrderPair h values).1
      (domain.naturalOrderPair h values).2)

/--
A coefficient-recursive radix-2 FFT producing values in natural order.

This is the standard Cooley-Tukey recursion on the even/odd coefficient split.
-/
noncomputable def fftNaturalAux :
    (k : Nat) ->
    (domain : Radix2Domain F) ->
    domain.logSize = k ->
    Polynomial F ->
    Fin domain.size -> F
  | 0, domain, hk, poly =>
      domain.toNTTSpec.transform poly
  | Nat.succ k, domain, hk, poly =>
      let hpos : 0 < domain.logSize := by
        simp [hk]
      let half := domain.succHalf hk
      let hkHalf : half.logSize = k := by
        simp [half]
      let evenVals := fftNaturalAux k half hkHalf (PolynomialParity.evenPart poly)
      let oddVals := fftNaturalAux k half hkHalf (PolynomialParity.oddPart poly)
      let stage := Radix2.butterflyValues
        (fun i => domain.point (domain.lowerIndex hpos i))
        evenVals oddVals
      domain.combineNaturalOrder hpos stage.1 stage.2

/--
The natural-order coefficient-recursive FFT on a concrete radix-2 domain.
-/
noncomputable def fftNatural (domain : Radix2Domain F) (poly : Polynomial F) :
    Fin domain.size -> F :=
  fftNaturalAux domain.logSize domain rfl poly

theorem fftNaturalAux_zero (domain : Radix2Domain F) (hk : domain.logSize = 0)
    (poly : Polynomial F) :
    fftNaturalAux 0 domain hk poly = domain.toNTTSpec.transform poly := by
  rfl

  theorem fftNaturalAux_succ (k : Nat) (domain : Radix2Domain F)
    (hk : domain.logSize = k + 1) (poly : Polynomial F) :
    fftNaturalAux (k + 1) domain hk poly =
      let hpos : 0 < domain.logSize := by simp [hk]
      let half := domain.succHalf hk
      let hkHalf : half.logSize = k := by
        simp [half]
      let evenVals := fftNaturalAux k half hkHalf (PolynomialParity.evenPart poly)
      let oddVals := fftNaturalAux k half hkHalf (PolynomialParity.oddPart poly)
      let stage := Radix2.butterflyValues
        (fun i => domain.point (domain.lowerIndex hpos i))
        evenVals oddVals
      domain.combineNaturalOrder hpos stage.1 stage.2 := by
  rfl

theorem fftNaturalAux_eq_transform :
    (k : Nat) ->
    (domain : Radix2Domain F) ->
    (hk : domain.logSize = k) ->
    (poly : Polynomial F) ->
    fftNaturalAux k domain hk poly = domain.toNTTSpec.transform poly
  | 0, domain, hk, poly => by
      rfl
  | k + 1, domain, hk, poly => by
      let hpos : 0 < domain.logSize := by
        simp [hk]
      let half := domain.succHalf hk
      have hkHalf : half.logSize = k := by
        simp [half]
      let stage :=
        Radix2.butterflyValues
          (fun i => domain.point (domain.lowerIndex hpos i))
          (fftNaturalAux k half hkHalf (PolynomialParity.evenPart poly))
          (fftNaturalAux k half hkHalf (PolynomialParity.oddPart poly))
      apply domain.naturalOrder_ext hpos
      calc
        domain.naturalOrderPair hpos (fftNaturalAux (k + 1) domain hk poly)
            = stage := by
                rw [fftNaturalAux_succ k domain hk poly]
                simpa [stage, hpos, half, hkHalf] using
                  (domain.naturalOrderPair_combineNaturalOrder hpos stage.1 stage.2)
        _ = Radix2.butterflyValues
              (fun i => domain.point (domain.lowerIndex hpos i))
              (half.toNTTSpec.transform (PolynomialParity.evenPart poly))
              (half.toNTTSpec.transform (PolynomialParity.oddPart poly)) := by
                dsimp [stage]
                rw [fftNaturalAux_eq_transform k half hkHalf (PolynomialParity.evenPart poly),
                  fftNaturalAux_eq_transform k half hkHalf (PolynomialParity.oddPart poly)]
        _ = domain.naturalOrderPair hpos (domain.toNTTSpec.transform poly) := by
              exact (transform_naturalOrder_eq_butterflyValues domain hpos poly).symm

theorem fftNatural_eq_transform (domain : Radix2Domain F) (poly : Polynomial F) :
    domain.fftNatural poly = domain.toNTTSpec.transform poly := by
  simpa [fftNatural] using fftNaturalAux_eq_transform domain.logSize domain rfl poly

end Radix2Domain

end Zklib.Core
