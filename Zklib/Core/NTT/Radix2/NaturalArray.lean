import Zklib.Core.NTT.Radix2.NaturalList

namespace Zklib.Core

namespace Radix2Domain

variable {F : Type*} [Field F]

/--
Interpret a size-indexed array as a table on `Fin n`.
-/
def tableOfArray {n : Nat} (values : Array F) (h : values.size = n) : Fin n -> F :=
  tableOfList values.toList (by rw [Array.length_toList, h])

omit [Field F] in
@[simp]
theorem tableOfArray_ofFn {n : Nat} (f : Fin n -> F) :
    tableOfArray (Array.ofFn f) (by simp) = f := by
  funext i
  simp [tableOfArray]

/--
Natural-order concatenation of lower and upper half-tables in array form.
-/
def combineNaturalOrderArray (domain : Radix2Domain F)
    (lower upper : Fin domain.halfSize -> F) : Array F :=
  Array.ofFn lower ++ Array.ofFn upper

@[simp]
theorem toList_combineNaturalOrderArray (domain : Radix2Domain F)
    (lower upper : Fin domain.halfSize -> F) :
    (domain.combineNaturalOrderArray lower upper).toList =
      domain.combineNaturalOrderList lower upper := by
  simp [combineNaturalOrderArray, combineNaturalOrderList]

@[simp]
theorem size_combineNaturalOrderArray (domain : Radix2Domain F) (h : 0 < domain.logSize)
    (lower upper : Fin domain.halfSize -> F) :
    (domain.combineNaturalOrderArray lower upper).size = domain.size := by
  rw [← Array.length_toList, toList_combineNaturalOrderArray]
  exact domain.length_combineNaturalOrderList h lower upper

/--
One natural-order radix-2 butterfly stage assembled from recursive array outputs.
-/
def butterflyStageArray (domain : Radix2Domain F) (h : 0 < domain.logSize)
    (lower upper : Array F)
    (hl : lower.size = domain.halfSize) (hu : upper.size = domain.halfSize) : Array F :=
  let stage :=
    Radix2.butterflyValues
      (fun i => domain.point (domain.lowerIndex h i))
      (tableOfArray lower hl)
      (tableOfArray upper hu)
  domain.combineNaturalOrderArray stage.1 stage.2

@[simp]
theorem toList_butterflyStageArray (domain : Radix2Domain F) (h : 0 < domain.logSize)
    (lower upper : Array F)
    (hl : lower.size = domain.halfSize) (hu : upper.size = domain.halfSize) :
    (domain.butterflyStageArray h lower upper hl hu).toList =
      domain.butterflyStageList h lower.toList upper.toList
        (by rw [Array.length_toList]; exact hl)
        (by rw [Array.length_toList]; exact hu) := by
  dsimp [butterflyStageArray, butterflyStageList, tableOfArray]
  simp [combineNaturalOrderArray, combineNaturalOrderList]

@[simp]
theorem size_butterflyStageArray (domain : Radix2Domain F) (h : 0 < domain.logSize)
    (lower upper : Array F)
    (hl : lower.size = domain.halfSize) (hu : upper.size = domain.halfSize) :
    (domain.butterflyStageArray h lower upper hl hu).size = domain.size := by
  rw [← Array.length_toList, toList_butterflyStageArray]
  exact domain.length_butterflyStageList h lower.toList upper.toList
    (by rw [Array.length_toList]; exact hl)
    (by rw [Array.length_toList]; exact hu)

/--
Array-based natural-order recursive radix-2 FFT carrying its output size.
-/
noncomputable def fftNaturalArrayAuxData :
    (k : Nat) ->
    (domain : Radix2Domain F) ->
    domain.logSize = k ->
    Polynomial F ->
    { values : Array F // values.size = domain.size }
  | 0, domain, hk, poly =>
      let zeroIdx : Fin domain.size := Fin.mk 0 domain.size_pos
      ⟨#[domain.toNTTSpec.transform poly zeroIdx], by
        have hsize : domain.size = 1 := by
          simpa [hk] using domain.size_eq_pow
        simp [hsize]⟩
  | Nat.succ k, domain, hk, poly =>
      let hpos : 0 < domain.logSize := by
        simp [hk]
      let half := domain.halfDomain hpos
      let hkHalf : half.logSize = k := by
        simp [half, Radix2Domain.halfDomain, hk]
      let evenValues := fftNaturalArrayAuxData k half hkHalf (PolynomialParity.evenPart poly)
      let oddValues := fftNaturalArrayAuxData k half hkHalf (PolynomialParity.oddPart poly)
      ⟨domain.butterflyStageArray hpos
          evenValues.1 oddValues.1 evenValues.2 oddValues.2,
        domain.size_butterflyStageArray hpos
          evenValues.1 oddValues.1 evenValues.2 oddValues.2⟩

/--
The array-based natural-order recursive radix-2 FFT with explicit recursive stages.
-/
noncomputable def fftNaturalArrayAux
    (k : Nat) (domain : Radix2Domain F) (hk : domain.logSize = k) (poly : Polynomial F) :
    Array F :=
  (fftNaturalArrayAuxData k domain hk poly).1

/--
The array-based natural-order recursive radix-2 FFT on a concrete domain.
-/
noncomputable def fftNaturalArray (domain : Radix2Domain F) (poly : Polynomial F) : Array F :=
  fftNaturalArrayAux domain.logSize domain rfl poly

theorem size_fftNaturalArrayAux
    (k : Nat) (domain : Radix2Domain F) (hk : domain.logSize = k) (poly : Polynomial F) :
    (fftNaturalArrayAux k domain hk poly).size = domain.size :=
  (fftNaturalArrayAuxData k domain hk poly).2

theorem size_fftNaturalArray (domain : Radix2Domain F) (poly : Polynomial F) :
    (domain.fftNaturalArray poly).size = domain.size := by
  simpa [fftNaturalArray] using size_fftNaturalArrayAux domain.logSize domain rfl poly

end Radix2Domain

end Zklib.Core
