import Mathlib.Data.List.OfFn
import Zklib.Core.NTT.Radix2.Flatten

namespace Zklib.Core

namespace Radix2

/--
Bit-reversal on `Fin (2^k)`, defined by recursively splitting the output
position into its left and right radix-2 halves.
-/
def bitRevAux : (k : Nat) -> Fin (2 ^ k) -> Fin (2 ^ k)
  | 0, _ =>
      Fin.mk 0 (by simp)
  | Nat.succ k, i =>
      if h : (i : Nat) < 2 ^ k then
        Fin.cast (by rw [pow_succ, Nat.mul_comm, Nat.two_mul])
          (evenIndex (2 ^ k) (bitRevAux k (Fin.castLT i h)))
      else
        let hle : 2 ^ k <= (i : Nat) := le_of_not_gt h
        let j : Fin (2 ^ k) :=
          Fin.mk ((i : Nat) - 2 ^ k)
            ((Nat.sub_lt_iff_lt_add hle).2
              (by simpa [pow_succ, Nat.mul_comm, Nat.two_mul] using i.isLt))
        Fin.cast (by rw [pow_succ, Nat.mul_comm, Nat.two_mul])
          (oddIndex (2 ^ k) (bitRevAux k j))

theorem bitRevAux_succ_left (k : Nat) (i : Fin (2 ^ (k + 1)))
    (h : (i : Nat) < 2 ^ k) :
    bitRevAux (k + 1) i =
      Fin.cast (by rw [pow_succ, Nat.mul_comm, Nat.two_mul])
        (evenIndex (2 ^ k) (bitRevAux k (Fin.castLT i h))) := by
  simp [bitRevAux, h]

theorem bitRevAux_succ_right (k : Nat) (i : Fin (2 ^ (k + 1)))
    (h : Not ((i : Nat) < 2 ^ k)) :
    bitRevAux (k + 1) i =
      let hle : 2 ^ k <= (i : Nat) := le_of_not_gt h
      let j : Fin (2 ^ k) :=
        Fin.mk ((i : Nat) - 2 ^ k)
          ((Nat.sub_lt_iff_lt_add hle).2
            (by simpa [pow_succ, Nat.mul_comm, Nat.two_mul] using i.isLt))
      Fin.cast (by rw [pow_succ, Nat.mul_comm, Nat.two_mul])
        (oddIndex (2 ^ k) (bitRevAux k j)) := by
  simp [bitRevAux, h]

theorem bitRevAux_succ_castAdd (k : Nat) (i : Fin (2 ^ k)) :
    bitRevAux (k + 1)
      (Fin.cast (by rw [pow_succ, Nat.mul_comm, Nat.two_mul]) (Fin.castAdd (2 ^ k) i)) =
      Fin.cast (by rw [pow_succ, Nat.mul_comm, Nat.two_mul])
        (evenIndex (2 ^ k) (bitRevAux k i)) := by
  have hlt :
      (((Fin.cast (by rw [pow_succ, Nat.mul_comm, Nat.two_mul]) (Fin.castAdd (2 ^ k) i) :
          Fin (2 ^ (k + 1))) : Nat) < 2 ^ k) := by
    simp [Fin.val_cast, Fin.val_castAdd]
  simpa [hlt] using bitRevAux_succ_left k
    (Fin.cast (by rw [pow_succ, Nat.mul_comm, Nat.two_mul]) (Fin.castAdd (2 ^ k) i)) hlt

theorem bitRevAux_succ_natAdd (k : Nat) (i : Fin (2 ^ k)) :
    bitRevAux (k + 1)
      (Fin.cast (by rw [pow_succ, Nat.mul_comm, Nat.two_mul]) (Fin.natAdd (2 ^ k) i)) =
      Fin.cast (by rw [pow_succ, Nat.mul_comm, Nat.two_mul])
        (oddIndex (2 ^ k) (bitRevAux k i)) := by
  let x : Fin (2 ^ (k + 1)) :=
    Fin.cast (by rw [pow_succ, Nat.mul_comm, Nat.two_mul]) (Fin.natAdd (2 ^ k) i)
  have hnot : Not (((x : Fin (2 ^ (k + 1))) : Nat) < 2 ^ k) := by
    simp [x, Fin.val_cast]
  rw [bitRevAux_succ_right k x hnot]
  simp [x, Fin.val_cast]

/--
The explicit bit-reversal order on `Fin (2^k)`, obtained by enumerating
`bitRevAux`.
-/
def bitRevOrderAux (k : Nat) : List (Fin (2 ^ k)) :=
  List.ofFn (bitRevAux k)

theorem length_bitRevOrderAux (k : Nat) :
    (bitRevOrderAux k).length = 2 ^ k := by
  simp [bitRevOrderAux]

theorem bitRevOrderAux_zero :
    bitRevOrderAux 0 = [Fin.mk 0 (by simp)] := by
  simp [bitRevOrderAux, bitRevAux]

theorem bitRevOrderAux_succ (k : Nat) :
    bitRevOrderAux (k + 1) =
      (bitRevOrderAux k).map
        (fun i => Fin.cast (by rw [pow_succ, Nat.mul_comm, Nat.two_mul]) (evenIndex (2 ^ k) i)) ++
      (bitRevOrderAux k).map
        (fun i => Fin.cast (by rw [pow_succ, Nat.mul_comm, Nat.two_mul]) (oddIndex (2 ^ k) i)) := by
  let hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
    rw [pow_succ, Nat.mul_comm, Nat.two_mul]
  let embedEven : Fin (2 ^ k) → Fin (2 ^ (k + 1)) :=
    fun i => Fin.cast hpow.symm (evenIndex (2 ^ k) i)
  let embedOdd : Fin (2 ^ k) → Fin (2 ^ (k + 1)) :=
    fun i => Fin.cast hpow.symm (oddIndex (2 ^ k) i)
  unfold bitRevOrderAux
  calc
    List.ofFn (bitRevAux (k + 1))
        = List.ofFn
            (fun i : Fin (2 ^ k + 2 ^ k) =>
              bitRevAux (k + 1) (Fin.cast hpow.symm i)) := by
              exact List.ofFn_congr hpow (bitRevAux (k + 1))
    _ = List.ofFn
          (Fin.append
            (fun i : Fin (2 ^ k) =>
              embedEven (bitRevAux k i))
            (fun i : Fin (2 ^ k) =>
              embedOdd (bitRevAux k i))) := by
            apply congrArg List.ofFn
            funext i
            refine Fin.addCases ?_ ?_ i
            · intro j
              simpa [embedEven, hpow] using (bitRevAux_succ_castAdd k j)
            · intro j
              rw [Fin.append_right]
              simpa [embedOdd, hpow] using (bitRevAux_succ_natAdd k j)
    _ = List.ofFn
          (fun i : Fin (2 ^ k) => embedEven (bitRevAux k i)) ++
        List.ofFn
          (fun i : Fin (2 ^ k) => embedOdd (bitRevAux k i)) := by
          rw [List.ofFn_fin_append]
    _ = (bitRevOrderAux k).map
          (fun i => Fin.cast (by rw [pow_succ, Nat.mul_comm, Nat.two_mul]) (evenIndex (2 ^ k) i)) ++
        (bitRevOrderAux k).map
          (fun i => Fin.cast (by rw [pow_succ, Nat.mul_comm, Nat.two_mul]) (oddIndex (2 ^ k) i)) := by
          have heven :
              List.ofFn (fun i : Fin (2 ^ k) => embedEven (bitRevAux k i)) =
                (bitRevOrderAux k).map embedEven := by
                simpa [bitRevOrderAux, Function.comp] using
                  (List.ofFn_comp' (f := bitRevAux k)
                    (g := embedEven))
          have hodd :
              List.ofFn (fun i : Fin (2 ^ k) => embedOdd (bitRevAux k i)) =
                (bitRevOrderAux k).map embedOdd := by
                simpa [bitRevOrderAux, Function.comp] using
                  (List.ofFn_comp' (f := bitRevAux k)
                    (g := embedOdd))
          rw [heven, hodd]

end Radix2

namespace Radix2Domain

variable {F : Type*} [Monoid F]

/--
Bit-reversal permutation on a concrete radix-2 domain, transported from the
canonical `Fin (2 ^ logSize)` index set.
-/
noncomputable def bitRevIndex (domain : Radix2Domain F) (i : Fin domain.size) : Fin domain.size :=
  Fin.cast domain.size_eq_pow.symm
    (Radix2.bitRevAux domain.logSize (Fin.cast domain.size_eq_pow i))

/--
The pointwise bit-reversal ordering obtained by enumerating `bitRevIndex`.
-/
noncomputable def bitRevOrderFn (domain : Radix2Domain F) : List (Fin domain.size) :=
  List.ofFn domain.bitRevIndex

theorem length_bitRevOrderFn (domain : Radix2Domain F) :
    domain.bitRevOrderFn.length = domain.size := by
  simp [bitRevOrderFn]

theorem bitRevOrderFn_eq_map_bitRevOrderAux (domain : Radix2Domain F) :
    domain.bitRevOrderFn =
      (Radix2.bitRevOrderAux domain.logSize).map (Fin.cast domain.size_eq_pow.symm) := by
  unfold bitRevOrderFn Radix2.bitRevOrderAux
  calc
    List.ofFn domain.bitRevIndex
        = List.ofFn
            (fun i : Fin (2 ^ domain.logSize) =>
              domain.bitRevIndex (Fin.cast domain.size_eq_pow.symm i)) := by
              exact List.ofFn_congr domain.size_eq_pow domain.bitRevIndex
    _ = List.ofFn
          (fun i : Fin (2 ^ domain.logSize) =>
            Fin.cast domain.size_eq_pow.symm (Radix2.bitRevAux domain.logSize i)) := by
          simp [bitRevIndex]
    _ = (List.ofFn (Radix2.bitRevAux domain.logSize)).map (Fin.cast domain.size_eq_pow.symm) := by
          symm
          simpa [Function.comp] using
            (List.ofFn_comp' (f := Radix2.bitRevAux domain.logSize)
              (g := Fin.cast domain.size_eq_pow.symm))

theorem evenIndex_eq_cast_evenIndex (domain : Radix2Domain F) (k : Nat)
    (hk : domain.logSize = k + 1) (i : Fin (2 ^ k)) :
    domain.evenIndex (by simp [hk]) (Fin.cast (by simp [Radix2Domain.halfSize, hk]) i) =
      Fin.cast (by
        have hsize : 2 ^ k + 2 ^ k = domain.size := by
          simpa [hk, pow_succ, Nat.mul_comm, Nat.two_mul] using domain.size_eq_pow.symm
        exact hsize)
        (Fin.cast (by simp) (Radix2.evenIndex (2 ^ k) i)) := by
  apply Fin.ext
  simp [Radix2Domain.evenIndex, Radix2Domain.halfSize, Radix2.evenIndex, Fin.val_cast]

theorem oddIndex_eq_cast_oddIndex (domain : Radix2Domain F) (k : Nat)
    (hk : domain.logSize = k + 1) (i : Fin (2 ^ k)) :
    domain.oddIndex (by simp [hk]) (Fin.cast (by simp [Radix2Domain.halfSize, hk]) i) =
      Fin.cast (by
        have hsize : 2 ^ k + 2 ^ k = domain.size := by
          simpa [hk, pow_succ, Nat.mul_comm, Nat.two_mul] using domain.size_eq_pow.symm
        exact hsize)
        (Fin.cast (by simp) (Radix2.oddIndex (2 ^ k) i)) := by
  apply Fin.ext
  simp [Radix2Domain.oddIndex, Radix2Domain.halfSize, Radix2.oddIndex, Fin.val_cast]

end Radix2Domain

namespace Radix2Domain

variable {F : Type*} [Field F]

/--
The recursion tree corresponding to the standard radix-2 bit-reversal
permutation on a concrete evaluation domain.
-/
noncomputable def bitRevTreeAux :
    (k : Nat) ->
    (domain : Radix2Domain F) ->
    domain.logSize = k ->
    Radix2.FFTTree (Fin domain.size)
  | k, domain, hk => indexTreeAux k domain hk

/--
The full bit-reversal recursion tree on a radix-2 domain.
-/
noncomputable def bitRevTree (domain : Radix2Domain F) : Radix2.FFTTree (Fin domain.size) :=
  bitRevTreeAux domain.logSize domain rfl

/--
The canonical bit-reversal ordering induced by the radix-2 recursion tree.
-/
noncomputable def bitRevOrder (domain : Radix2Domain F) : List (Fin domain.size) :=
  domain.bitRevTree.flatten

theorem bitRevTreeAux_eq_indexTreeAux (k : Nat) (domain : Radix2Domain F)
    (hk : domain.logSize = k) :
    bitRevTreeAux k domain hk = indexTreeAux k domain hk := by
  rfl

theorem bitRevTree_eq_indexTree (domain : Radix2Domain F) :
    domain.bitRevTree = domain.indexTree := by
  rfl

theorem bitRevOrder_eq_indexOrder (domain : Radix2Domain F) :
    domain.bitRevOrder = domain.indexOrder := by
  rfl

theorem indexTreeAux_flatten_eq_map_bitRevOrderAux :
    (k : Nat) ->
    (domain : Radix2Domain F) ->
    (hk : domain.logSize = k) ->
    (indexTreeAux k domain hk).flatten =
      (Radix2.bitRevOrderAux k).map
        (Fin.cast (by simpa [hk] using domain.size_eq_pow.symm))
  | 0, domain, hk => by
      have hsize : domain.size = 1 := by
        simpa [hk] using domain.size_eq_pow
      calc
        (indexTreeAux 0 domain hk).flatten
            = [Fin.mk 0 domain.size_pos] := by
                rfl
        _ = [Fin.cast (by simpa [hk] using domain.size_eq_pow.symm) (Fin.mk 0 (by simp))] := by
              apply congrArg List.singleton
              apply Fin.ext
              simp [Fin.val_cast]
        _ = (Radix2.bitRevOrderAux 0).map
              (Fin.cast (by simpa [hk] using domain.size_eq_pow.symm)) := by
              simp [Radix2.bitRevOrderAux_zero]
  | k + 1, domain, hk => by
      let hpos : 0 < domain.logSize := by
        simp [hk]
      let half := domain.halfDomain hpos
      have hkHalf : half.logSize = k := by
        simp [half, Radix2Domain.halfDomain, hk]
      have hhalfSize : 2 ^ k = half.size := by
        simpa [half, Radix2Domain.halfDomain, hk] using half.size_eq_pow.symm
      have hpow : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by
        simp [pow_succ, Nat.mul_comm, Nat.two_mul]
      have hdom : 2 ^ (k + 1) = domain.size := by
        simpa [hk] using domain.size_eq_pow.symm
      let castEven : Fin (2 ^ k) -> Fin domain.size :=
        fun i =>
          Fin.cast hdom
            (Fin.cast hpow (Radix2.evenIndex (2 ^ k) i))
      let castOdd : Fin (2 ^ k) -> Fin domain.size :=
        fun i =>
          Fin.cast hdom
            (Fin.cast hpow (Radix2.oddIndex (2 ^ k) i))
      have hrec :
          (indexTreeAux (k + 1) domain hk).flatten =
            (Radix2.FFTTree.map (domain.evenIndex hpos) (indexTreeAux k half hkHalf)).flatten ++
            (Radix2.FFTTree.map (domain.oddIndex hpos) (indexTreeAux k half hkHalf)).flatten := by
        simpa [half, hkHalf, Radix2.FFTTree.flatten] using
          congrArg Radix2.FFTTree.flatten (indexTreeAux_succ k domain hk)
      have hEven :
          (Radix2.FFTTree.map (domain.evenIndex hpos) (indexTreeAux k half hkHalf)).flatten =
            (Radix2.bitRevOrderAux k).map castEven := by
        rw [Radix2.FFTTree.flatten_map]
        have hNested :=
          congrArg (List.map (domain.evenIndex hpos))
            (indexTreeAux_flatten_eq_map_bitRevOrderAux k half hkHalf)
        have hNested' :
            List.map (domain.evenIndex hpos) (indexTreeAux k half hkHalf).flatten =
              List.map (domain.evenIndex hpos ∘ Fin.cast hhalfSize) (Radix2.bitRevOrderAux k) := by
          convert hNested using 1
          symm
          exact List.map_map
        calc
          List.map (domain.evenIndex hpos) (indexTreeAux k half hkHalf).flatten =
              List.map (domain.evenIndex hpos ∘ Fin.cast hhalfSize)
                (Radix2.bitRevOrderAux k) := hNested'
          _ = (Radix2.bitRevOrderAux k).map castEven := by
                have hfun :
                    ∀ i : Fin (2 ^ k),
                      domain.evenIndex hpos (Fin.cast hhalfSize i) = castEven i := by
                  intro i
                  simpa [castEven, hhalfSize, hpow, hdom, hpos] using
                    (evenIndex_eq_cast_evenIndex (domain := domain) k hk i)
                apply List.map_congr_left
                intro i hi
                simp [Function.comp, hfun i]
      have hOdd :
          (Radix2.FFTTree.map (domain.oddIndex hpos) (indexTreeAux k half hkHalf)).flatten =
            (Radix2.bitRevOrderAux k).map castOdd := by
        rw [Radix2.FFTTree.flatten_map]
        have hNested :=
          congrArg (List.map (domain.oddIndex hpos))
            (indexTreeAux_flatten_eq_map_bitRevOrderAux k half hkHalf)
        have hNested' :
            List.map (domain.oddIndex hpos) (indexTreeAux k half hkHalf).flatten =
              List.map (domain.oddIndex hpos ∘ Fin.cast hhalfSize) (Radix2.bitRevOrderAux k) := by
          convert hNested using 1
          symm
          exact List.map_map
        calc
          List.map (domain.oddIndex hpos) (indexTreeAux k half hkHalf).flatten =
              List.map (domain.oddIndex hpos ∘ Fin.cast hhalfSize)
                (Radix2.bitRevOrderAux k) := hNested'
          _ = (Radix2.bitRevOrderAux k).map castOdd := by
                have hfun :
                    ∀ i : Fin (2 ^ k),
                      domain.oddIndex hpos (Fin.cast hhalfSize i) = castOdd i := by
                  intro i
                  simpa [castOdd, hhalfSize, hpow, hdom, hpos] using
                    (oddIndex_eq_cast_oddIndex (domain := domain) k hk i)
                apply List.map_congr_left
                intro i hi
                simp [Function.comp, hfun i]
      calc
        (indexTreeAux (k + 1) domain hk).flatten
            = (Radix2.FFTTree.map (domain.evenIndex hpos) (indexTreeAux k half hkHalf)).flatten ++
              (Radix2.FFTTree.map (domain.oddIndex hpos) (indexTreeAux k half hkHalf)).flatten := hrec
        _ = (Radix2.bitRevOrderAux k).map castEven ++
              (Radix2.bitRevOrderAux k).map castOdd := by
                rw [hEven, hOdd]
        _ = (Radix2.bitRevOrderAux (k + 1)).map
              (Fin.cast (by simpa [hk] using domain.size_eq_pow.symm)) := by
                rw [Radix2.bitRevOrderAux_succ, List.map_append]
                have hComposeEven :
                    (List.map (fun i => Fin.cast hpow (Radix2.evenIndex (2 ^ k) i))
                      (Radix2.bitRevOrderAux k)).map (Fin.cast hdom) =
                      List.map castEven (Radix2.bitRevOrderAux k) := by
                  rw [List.map_map]
                  apply List.map_congr_left
                  intro i hi
                  rfl
                have hComposeOdd :
                    (List.map (fun i => Fin.cast hpow (Radix2.oddIndex (2 ^ k) i))
                      (Radix2.bitRevOrderAux k)).map (Fin.cast hdom) =
                      List.map castOdd (Radix2.bitRevOrderAux k) := by
                  rw [List.map_map]
                  apply List.map_congr_left
                  intro i hi
                  rfl
                rw [hComposeEven, hComposeOdd]

theorem bitRevOrder_eq_map_bitRevOrderAux (domain : Radix2Domain F) :
    domain.bitRevOrder =
      (Radix2.bitRevOrderAux domain.logSize).map (Fin.cast domain.size_eq_pow.symm) := by
  simpa [bitRevOrder, bitRevTree, bitRevTreeAux] using
    indexTreeAux_flatten_eq_map_bitRevOrderAux domain.logSize domain rfl

theorem bitRevOrderFn_eq_bitRevOrder (domain : Radix2Domain F) :
    domain.bitRevOrderFn = domain.bitRevOrder := by
  rw [bitRevOrderFn_eq_map_bitRevOrderAux, bitRevOrder_eq_map_bitRevOrderAux]

theorem bitRevOrder_eq_bitRevOrderFn (domain : Radix2Domain F) :
    domain.bitRevOrder = domain.bitRevOrderFn := by
  rw [bitRevOrderFn_eq_bitRevOrder]

theorem indexOrder_eq_bitRevOrder (domain : Radix2Domain F) :
    domain.indexOrder = domain.bitRevOrder := by
  rw [bitRevOrder_eq_indexOrder]

theorem length_bitRevOrder (domain : Radix2Domain F) :
    domain.bitRevOrder.length = domain.size := by
  rw [bitRevOrder_eq_indexOrder]
  exact length_indexOrder domain

theorem valuesInParityOrder_eq_map_transform_bitRevOrder (domain : Radix2Domain F)
    (poly : Polynomial F) :
    domain.valuesInParityOrder poly =
      domain.bitRevOrder.map (fun i => domain.toNTTSpec.transform poly i) := by
  rw [bitRevOrder_eq_indexOrder]
  exact valuesInParityOrder_eq_map_transform_indexOrder domain poly

theorem valuesInParityOrder_eq_map_transform_bitRevOrderFn (domain : Radix2Domain F)
    (poly : Polynomial F) :
    domain.valuesInParityOrder poly =
      domain.bitRevOrderFn.map (fun i => domain.toNTTSpec.transform poly i) := by
  rw [bitRevOrderFn_eq_bitRevOrder]
  exact valuesInParityOrder_eq_map_transform_bitRevOrder domain poly

end Radix2Domain

end Zklib.Core
