import Zklib.Core.NTT.Radix2.CosetNaturalList
import Zklib.Core.NTT.Radix2.NaturalArray

namespace Zklib.Core

namespace CosetRadix2Domain

variable {F : Type*} [Field F]

/--
Natural-order concatenation of lower and upper half-tables in array form for a
coset radix-2 domain.
-/
def combineNaturalOrderArray (domain : CosetRadix2Domain F)
    (lower upper : Fin domain.base.halfSize -> F) : Array F :=
  domain.base.combineNaturalOrderArray lower upper

@[simp]
theorem toList_combineNaturalOrderArray (domain : CosetRadix2Domain F)
    (lower upper : Fin domain.base.halfSize -> F) :
    (domain.combineNaturalOrderArray lower upper).toList =
      domain.combineNaturalOrderList lower upper := by
  simp [combineNaturalOrderArray, combineNaturalOrderList]

theorem combineNaturalOrderArray_eq_arrayOfTable (domain : CosetRadix2Domain F)
    (h : 0 < domain.base.logSize) (lower upper : Fin domain.base.halfSize -> F) :
    domain.combineNaturalOrderArray lower upper =
      Radix2Representation.arrayOfTable (domain.base.combineNaturalOrder h lower upper) := by
  apply Array.ext'
  rw [Radix2Representation.arrayOfTable_toList, domain.toList_combineNaturalOrderArray]
  exact domain.combineNaturalOrderList_eq_listOfTable h lower upper

@[simp]
theorem size_combineNaturalOrderArray (domain : CosetRadix2Domain F)
    (h : 0 < domain.base.logSize) (lower upper : Fin domain.base.halfSize -> F) :
    (domain.combineNaturalOrderArray lower upper).size = domain.base.size := by
  rw [← Array.length_toList, domain.toList_combineNaturalOrderArray]
  exact domain.length_combineNaturalOrderList h lower upper

/--
One natural-order radix-2 butterfly stage assembled from recursive array
outputs on a coset domain.
-/
def butterflyStageArray (domain : CosetRadix2Domain F) (h : 0 < domain.base.logSize)
    (lower upper : Array F)
    (hl : lower.size = domain.base.halfSize) (hu : upper.size = domain.base.halfSize) :
    Array F :=
  let stage :=
    Radix2.butterflyValues
      (fun i => domain.point (domain.base.lowerIndex h i))
      (Radix2Domain.tableOfArray lower hl)
      (Radix2Domain.tableOfArray upper hu)
  domain.combineNaturalOrderArray stage.1 stage.2

@[simp]
theorem toList_butterflyStageArray (domain : CosetRadix2Domain F) (h : 0 < domain.base.logSize)
    (lower upper : Array F)
    (hl : lower.size = domain.base.halfSize) (hu : upper.size = domain.base.halfSize) :
    (domain.butterflyStageArray h lower upper hl hu).toList =
      domain.butterflyStageList h lower.toList upper.toList
        (by rw [Array.length_toList]; exact hl)
        (by rw [Array.length_toList]; exact hu) := by
  have hLowerTable :
      Radix2Domain.tableOfArray lower hl =
        Radix2Domain.tableOfList lower.toList (by rw [Array.length_toList]; exact hl) := by
    exact Radix2Representation.tableOfArray_eq_tableOfList_toList (values := lower) (h := hl)
  have hUpperTable :
      Radix2Domain.tableOfArray upper hu =
        Radix2Domain.tableOfList upper.toList (by rw [Array.length_toList]; exact hu) := by
    exact Radix2Representation.tableOfArray_eq_tableOfList_toList (values := upper) (h := hu)
  dsimp [butterflyStageArray, butterflyStageList]
  rw [hLowerTable, hUpperTable]
  simp [combineNaturalOrderArray, combineNaturalOrderList]

theorem butterflyStageArray_eq_arrayOfTable (domain : CosetRadix2Domain F)
    (h : 0 < domain.base.logSize) (lower upper : Fin domain.base.halfSize -> F) :
    domain.butterflyStageArray h
      (Array.ofFn lower) (Array.ofFn upper)
      (by simp) (by simp) =
        Radix2Representation.arrayOfTable
          (domain.base.combineNaturalOrder h
            (Radix2.butterflyValues
              (fun i => domain.point (domain.base.lowerIndex h i))
              lower upper).1
            (Radix2.butterflyValues
              (fun i => domain.point (domain.base.lowerIndex h i))
              lower upper).2) := by
  apply Array.ext'
  rw [Radix2Representation.arrayOfTable_toList, domain.toList_butterflyStageArray]
  simpa [Radix2Representation.listOfTable] using
    domain.butterflyStageList_eq_listOfTable h lower upper

@[simp]
theorem size_butterflyStageArray (domain : CosetRadix2Domain F) (h : 0 < domain.base.logSize)
    (lower upper : Array F)
    (hl : lower.size = domain.base.halfSize) (hu : upper.size = domain.base.halfSize) :
    (domain.butterflyStageArray h lower upper hl hu).size = domain.base.size := by
  rw [← Array.length_toList, domain.toList_butterflyStageArray]
  exact domain.length_butterflyStageList h lower.toList upper.toList
    (by rw [Array.length_toList]; exact hl)
    (by rw [Array.length_toList]; exact hu)

/--
Array-based natural-order recursive radix-2 FFT on a coset domain, carrying
its output size.
-/
noncomputable def fftNaturalArrayAuxData :
    (k : Nat) ->
    (domain : CosetRadix2Domain F) ->
    domain.base.logSize = k ->
    Polynomial F ->
    { values : Array F // values.size = domain.base.size }
  | 0, domain, hk, poly =>
      let zeroIdx : Fin domain.base.size := Fin.mk 0 domain.base.size_pos
      ⟨#[domain.toCosetNTTSpec.transform poly zeroIdx], by
        have hsize : domain.base.size = 1 := by
          simpa [hk] using domain.base.size_eq_pow
        simp [hsize]⟩
  | Nat.succ k, domain, hk, poly =>
      let hpos : 0 < domain.base.logSize := by
        simp [hk]
      let half := domain.succHalfSquare hk
      let hkHalf : half.base.logSize = k := by
        simp [half]
      let evenValues := fftNaturalArrayAuxData k half hkHalf (PolynomialParity.evenPart poly)
      let oddValues := fftNaturalArrayAuxData k half hkHalf (PolynomialParity.oddPart poly)
      ⟨domain.butterflyStageArray hpos
          evenValues.1 oddValues.1 evenValues.2 oddValues.2,
        domain.size_butterflyStageArray hpos
          evenValues.1 oddValues.1 evenValues.2 oddValues.2⟩

/--
The array-based natural-order recursive radix-2 FFT with explicit recursive
stages on a coset domain.
-/
noncomputable def fftNaturalArrayAux
    (k : Nat) (domain : CosetRadix2Domain F) (hk : domain.base.logSize = k)
    (poly : Polynomial F) : Array F :=
  (fftNaturalArrayAuxData k domain hk poly).1

/--
The array-based natural-order recursive radix-2 FFT on a concrete coset domain.
-/
noncomputable def fftNaturalArray (domain : CosetRadix2Domain F) (poly : Polynomial F) : Array F :=
  fftNaturalArrayAux domain.base.logSize domain rfl poly

theorem size_fftNaturalArrayAux
    (k : Nat) (domain : CosetRadix2Domain F) (hk : domain.base.logSize = k)
    (poly : Polynomial F) :
    (fftNaturalArrayAux k domain hk poly).size = domain.base.size :=
  (fftNaturalArrayAuxData k domain hk poly).2

theorem size_fftNaturalArray (domain : CosetRadix2Domain F) (poly : Polynomial F) :
    (domain.fftNaturalArray poly).size = domain.base.size := by
  simpa [fftNaturalArray] using size_fftNaturalArrayAux domain.base.logSize domain rfl poly

end CosetRadix2Domain

end Zklib.Core
