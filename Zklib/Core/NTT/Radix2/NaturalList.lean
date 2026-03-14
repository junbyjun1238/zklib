import Zklib.Core.NTT.Radix2.Natural
import Zklib.Core.NTT.Radix2.Representation

namespace Zklib.Core

namespace Radix2Domain

variable {F : Type*} [Field F]

/--
Interpret a length-indexed list as a table on `Fin n`.
-/
abbrev tableOfList {n : Nat} (values : List F) (h : values.length = n) : Fin n -> F :=
  Radix2Representation.tableOfList values h

omit [Field F] in
@[simp]
theorem tableOfList_ofFn {n : Nat} (f : Fin n -> F) :
    tableOfList (List.ofFn f) (List.length_ofFn (f := f)) = f := by
  simpa [tableOfList, Radix2Representation.listOfTable] using
    (Radix2Representation.tableOfList_listOfTable (values := f))

/--
Natural-order concatenation of lower and upper half-tables.
-/
def combineNaturalOrderList (domain : Radix2Domain F)
    (lower upper : Fin domain.halfSize -> F) : List F :=
  List.ofFn lower ++ List.ofFn upper

@[simp]
theorem length_combineNaturalOrderList (domain : Radix2Domain F) (h : 0 < domain.logSize)
    (lower upper : Fin domain.halfSize -> F) :
    (domain.combineNaturalOrderList lower upper).length = domain.size := by
  simp [combineNaturalOrderList, domain.size_eq_halfSize_add_halfSize h]

theorem combineNaturalOrderList_eq_ofFn (domain : Radix2Domain F) (h : 0 < domain.logSize)
    (lower upper : Fin domain.halfSize -> F) :
    domain.combineNaturalOrderList lower upper =
      List.ofFn (domain.combineNaturalOrder h lower upper) := by
  have hsize : domain.halfSize + domain.halfSize = domain.size :=
    (domain.size_eq_halfSize_add_halfSize h).symm
  calc
    domain.combineNaturalOrderList lower upper
        = List.ofFn (Fin.append lower upper) := by
            rw [combineNaturalOrderList]
            exact (List.ofFn_fin_append lower upper).symm
    _ = List.ofFn (fun i : Fin domain.size =>
          Fin.append lower upper (Fin.cast hsize.symm i)) := by
            rw [List.ofFn_congr (h := hsize) (f := Fin.append lower upper)]
    _ = List.ofFn (domain.combineNaturalOrder h lower upper) := by
          rfl

theorem combineNaturalOrderList_eq_listOfTable (domain : Radix2Domain F) (h : 0 < domain.logSize)
    (lower upper : Fin domain.halfSize -> F) :
    domain.combineNaturalOrderList lower upper =
      Radix2Representation.listOfTable (domain.combineNaturalOrder h lower upper) := by
  simpa [Radix2Representation.listOfTable] using
    domain.combineNaturalOrderList_eq_ofFn h lower upper

/--
One natural-order radix-2 butterfly stage assembled from recursive list outputs.
-/
def butterflyStageList (domain : Radix2Domain F) (h : 0 < domain.logSize)
    (lower upper : List F)
    (hl : lower.length = domain.halfSize) (hu : upper.length = domain.halfSize) : List F :=
  let stage :=
    Radix2.butterflyValues
      (fun i => domain.point (domain.lowerIndex h i))
      (tableOfList lower hl)
      (tableOfList upper hu)
  domain.combineNaturalOrderList stage.1 stage.2

@[simp]
theorem length_butterflyStageList (domain : Radix2Domain F) (h : 0 < domain.logSize)
    (lower upper : List F)
    (hl : lower.length = domain.halfSize) (hu : upper.length = domain.halfSize) :
    (domain.butterflyStageList h lower upper hl hu).length = domain.size := by
  dsimp [butterflyStageList]
  simpa using
    (domain.length_combineNaturalOrderList h
      (Radix2.butterflyValues
        (fun i => domain.point (domain.lowerIndex h i))
        (tableOfList lower hl)
        (tableOfList upper hu)).1
      (Radix2.butterflyValues
        (fun i => domain.point (domain.lowerIndex h i))
        (tableOfList lower hl)
        (tableOfList upper hu)).2)

theorem butterflyStageList_congr (domain : Radix2Domain F) (h : 0 < domain.logSize)
    {lower lower' upper upper' : List F}
    {hl : lower.length = domain.halfSize} {hu : upper.length = domain.halfSize}
    {hl' : lower'.length = domain.halfSize} {hu' : upper'.length = domain.halfSize}
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

theorem butterflyStageList_eq_ofFn (domain : Radix2Domain F) (h : 0 < domain.logSize)
    (lower upper : Fin domain.halfSize -> F) :
    domain.butterflyStageList h
      (List.ofFn lower) (List.ofFn upper)
      (List.length_ofFn (f := lower)) (List.length_ofFn (f := upper)) =
        List.ofFn
          (domain.combineNaturalOrder h
            (Radix2.butterflyValues
              (fun i => domain.point (domain.lowerIndex h i))
              lower upper).1
            (Radix2.butterflyValues
              (fun i => domain.point (domain.lowerIndex h i))
              lower upper).2) := by
  dsimp [butterflyStageList]
  simpa using
    (domain.combineNaturalOrderList_eq_ofFn h
      (Radix2.butterflyValues
        (fun i => domain.point (domain.lowerIndex h i))
        lower upper).1
      (Radix2.butterflyValues
        (fun i => domain.point (domain.lowerIndex h i))
        lower upper).2)

theorem butterflyStageList_eq_listOfTable (domain : Radix2Domain F) (h : 0 < domain.logSize)
    (lower upper : Fin domain.halfSize -> F) :
    domain.butterflyStageList h
      (List.ofFn lower) (List.ofFn upper)
      (List.length_ofFn (f := lower)) (List.length_ofFn (f := upper)) =
        Radix2Representation.listOfTable
          (domain.combineNaturalOrder h
            (Radix2.butterflyValues
              (fun i => domain.point (domain.lowerIndex h i))
              lower upper).1
            (Radix2.butterflyValues
              (fun i => domain.point (domain.lowerIndex h i))
              lower upper).2) := by
  simpa [Radix2Representation.listOfTable] using domain.butterflyStageList_eq_ofFn h lower upper

/--
List-based natural-order recursive radix-2 FFT carrying its output length.
-/
noncomputable def fftNaturalListAuxData :
    (k : Nat) ->
    (domain : Radix2Domain F) ->
    domain.logSize = k ->
    Polynomial F ->
    { values : List F // values.length = domain.size }
  | 0, domain, hk, poly =>
      let zeroIdx : Fin domain.size := Fin.mk 0 domain.size_pos
      ⟨[domain.toNTTSpec.transform poly zeroIdx], by
        have hsize : domain.size = 1 := by
          simpa [hk] using domain.size_eq_pow
        simp [hsize]⟩
  | Nat.succ k, domain, hk, poly =>
      let hpos : 0 < domain.logSize := by
        simp [hk]
      let half := domain.succHalf hk
      let hkHalf : half.logSize = k := by
        simp [half]
      let evenValues := fftNaturalListAuxData k half hkHalf (PolynomialParity.evenPart poly)
      let oddValues := fftNaturalListAuxData k half hkHalf (PolynomialParity.oddPart poly)
      ⟨domain.butterflyStageList hpos
          evenValues.1 oddValues.1 evenValues.2 oddValues.2,
        domain.length_butterflyStageList hpos
          evenValues.1 oddValues.1 evenValues.2 oddValues.2⟩

/--
The list-based natural-order recursive radix-2 FFT with explicit recursive stages.
-/
noncomputable def fftNaturalListAux
    (k : Nat) (domain : Radix2Domain F) (hk : domain.logSize = k) (poly : Polynomial F) :
    List F :=
  (fftNaturalListAuxData k domain hk poly).1

/--
The list-based natural-order recursive radix-2 FFT on a concrete domain.
-/
noncomputable def fftNaturalList (domain : Radix2Domain F) (poly : Polynomial F) : List F :=
  fftNaturalListAux domain.logSize domain rfl poly

theorem length_fftNaturalListAux
    (k : Nat) (domain : Radix2Domain F) (hk : domain.logSize = k) (poly : Polynomial F) :
    (fftNaturalListAux k domain hk poly).length = domain.size :=
  (fftNaturalListAuxData k domain hk poly).2

theorem length_fftNaturalList (domain : Radix2Domain F) (poly : Polynomial F) :
    (domain.fftNaturalList poly).length = domain.size := by
  simpa [fftNaturalList] using length_fftNaturalListAux domain.logSize domain rfl poly

end Radix2Domain

end Zklib.Core
