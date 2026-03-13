import Zklib.Core.NTT.Radix2.CosetNatural
import Zklib.Core.NTT.Radix2.NaturalList

namespace Zklib.Core

namespace CosetRadix2Domain

variable {F : Type*} [Field F]

/--
Natural-order concatenation of lower and upper half-tables for a coset radix-2
domain.
-/
def combineNaturalOrderList (domain : CosetRadix2Domain F)
    (lower upper : Fin domain.base.halfSize -> F) : List F :=
  domain.base.combineNaturalOrderList lower upper

@[simp]
theorem length_combineNaturalOrderList (domain : CosetRadix2Domain F)
    (h : 0 < domain.base.logSize) (lower upper : Fin domain.base.halfSize -> F) :
    (domain.combineNaturalOrderList lower upper).length = domain.base.size := by
  simpa [combineNaturalOrderList] using
    (domain.base.length_combineNaturalOrderList h lower upper)

theorem combineNaturalOrderList_eq_ofFn (domain : CosetRadix2Domain F)
    (h : 0 < domain.base.logSize) (lower upper : Fin domain.base.halfSize -> F) :
    domain.combineNaturalOrderList lower upper =
      List.ofFn (domain.base.combineNaturalOrder h lower upper) := by
  simpa [combineNaturalOrderList] using
    (domain.base.combineNaturalOrderList_eq_ofFn h lower upper)

/--
One natural-order radix-2 butterfly stage assembled from recursive list outputs
on a coset domain.
-/
def butterflyStageList (domain : CosetRadix2Domain F) (h : 0 < domain.base.logSize)
    (lower upper : List F)
    (hl : lower.length = domain.base.halfSize) (hu : upper.length = domain.base.halfSize) :
    List F :=
  let stage :=
    Radix2.butterflyValues
      (fun i => domain.point (domain.base.lowerIndex h i))
      (Radix2Domain.tableOfList lower hl)
      (Radix2Domain.tableOfList upper hu)
  domain.combineNaturalOrderList stage.1 stage.2

@[simp]
theorem length_butterflyStageList (domain : CosetRadix2Domain F) (h : 0 < domain.base.logSize)
    (lower upper : List F)
    (hl : lower.length = domain.base.halfSize) (hu : upper.length = domain.base.halfSize) :
    (domain.butterflyStageList h lower upper hl hu).length = domain.base.size := by
  dsimp [butterflyStageList]
  simpa using
    (domain.length_combineNaturalOrderList h
      (Radix2.butterflyValues
        (fun i => domain.point (domain.base.lowerIndex h i))
        (Radix2Domain.tableOfList lower hl)
        (Radix2Domain.tableOfList upper hu)).1
      (Radix2.butterflyValues
        (fun i => domain.point (domain.base.lowerIndex h i))
        (Radix2Domain.tableOfList lower hl)
        (Radix2Domain.tableOfList upper hu)).2)

theorem butterflyStageList_congr (domain : CosetRadix2Domain F) (h : 0 < domain.base.logSize)
    {lower lower' upper upper' : List F}
    {hl : lower.length = domain.base.halfSize} {hu : upper.length = domain.base.halfSize}
    {hl' : lower'.length = domain.base.halfSize} {hu' : upper'.length = domain.base.halfSize}
    (hlower : lower = lower') (hupper : upper = upper') :
    domain.butterflyStageList h lower upper hl hu =
      domain.butterflyStageList h lower' upper' hl' hu' := by
  subst hlower
  subst hupper
  have hhl : hl = hl' := by
    apply Subsingleton.elim
  have hhu : hu = hu' := by
    apply Subsingleton.elim
  subst hhl
  subst hhu
  rfl

theorem butterflyStageList_eq_ofFn (domain : CosetRadix2Domain F)
    (h : 0 < domain.base.logSize) (lower upper : Fin domain.base.halfSize -> F) :
    domain.butterflyStageList h
      (List.ofFn lower) (List.ofFn upper)
      (List.length_ofFn (f := lower)) (List.length_ofFn (f := upper)) =
        List.ofFn
          (domain.base.combineNaturalOrder h
            (Radix2.butterflyValues
              (fun i => domain.point (domain.base.lowerIndex h i))
              lower upper).1
            (Radix2.butterflyValues
              (fun i => domain.point (domain.base.lowerIndex h i))
              lower upper).2) := by
  dsimp [butterflyStageList]
  simpa using
    (domain.combineNaturalOrderList_eq_ofFn h
      (Radix2.butterflyValues
        (fun i => domain.point (domain.base.lowerIndex h i))
        lower upper).1
      (Radix2.butterflyValues
        (fun i => domain.point (domain.base.lowerIndex h i))
        lower upper).2)

/--
List-based natural-order recursive radix-2 FFT on a coset domain, carrying its
output length.
-/
noncomputable def fftNaturalListAuxData :
    (k : Nat) ->
    (domain : CosetRadix2Domain F) ->
    domain.base.logSize = k ->
    Polynomial F ->
    { values : List F // values.length = domain.base.size }
  | 0, domain, hk, poly =>
      let zeroIdx : Fin domain.base.size := Fin.mk 0 domain.base.size_pos
      ⟨[domain.toCosetNTTSpec.transform poly zeroIdx], by
        have hsize : domain.base.size = 1 := by
          simpa [hk] using domain.base.size_eq_pow
        simp [hsize]⟩
  | Nat.succ k, domain, hk, poly =>
      let hpos : 0 < domain.base.logSize := by
        simp [hk]
      let half := domain.halfSquareDomain hpos
      let hkHalf : half.base.logSize = k := by
        simp [half, CosetRadix2Domain.halfSquareDomain, Radix2Domain.halfDomain, hk]
      let evenValues := fftNaturalListAuxData k half hkHalf (PolynomialParity.evenPart poly)
      let oddValues := fftNaturalListAuxData k half hkHalf (PolynomialParity.oddPart poly)
      ⟨domain.butterflyStageList hpos
          evenValues.1 oddValues.1 evenValues.2 oddValues.2,
        domain.length_butterflyStageList hpos
          evenValues.1 oddValues.1 evenValues.2 oddValues.2⟩

/--
The list-based natural-order recursive radix-2 FFT with explicit recursive
stages on a coset domain.
-/
noncomputable def fftNaturalListAux
    (k : Nat) (domain : CosetRadix2Domain F) (hk : domain.base.logSize = k)
    (poly : Polynomial F) : List F :=
  (fftNaturalListAuxData k domain hk poly).1

/--
The list-based natural-order recursive radix-2 FFT on a concrete coset domain.
-/
noncomputable def fftNaturalList (domain : CosetRadix2Domain F) (poly : Polynomial F) : List F :=
  fftNaturalListAux domain.base.logSize domain rfl poly

theorem length_fftNaturalListAux
    (k : Nat) (domain : CosetRadix2Domain F) (hk : domain.base.logSize = k)
    (poly : Polynomial F) :
    (fftNaturalListAux k domain hk poly).length = domain.base.size :=
  (fftNaturalListAuxData k domain hk poly).2

theorem length_fftNaturalList (domain : CosetRadix2Domain F) (poly : Polynomial F) :
    (domain.fftNaturalList poly).length = domain.base.size := by
  simpa [fftNaturalList] using length_fftNaturalListAux domain.base.logSize domain rfl poly

end CosetRadix2Domain

end Zklib.Core
