import Zklib.Core.NTT.Radix2.Tree

namespace Zklib.Core

namespace Radix2Domain

variable {F : Type*} [Field F]

/--
The recursion tree of evaluation indices visited by the radix-2 parity split.

This records the output permutation induced by repeatedly taking even indices
first and odd indices second. Later files can flatten this tree into a
bit-reversed output table without changing the recursive structure.
-/
noncomputable def indexTreeAux :
    (k : Nat) ->
    (domain : Radix2Domain F) ->
    domain.logSize = k ->
    Radix2.FFTTree (Fin domain.size)
  | 0, domain, hk =>
      Radix2.FFTTree.leaf (Fin.mk 0 domain.size_pos)
  | Nat.succ k, domain, hk =>
      let hpos : 0 < domain.logSize := by simp [hk]
      let half := domain.succHalf hk
      Radix2.FFTTree.node
        (Radix2.FFTTree.map (domain.evenIndex hpos)
          (indexTreeAux k half (by simp [half])))
        (Radix2.FFTTree.map (domain.oddIndex hpos)
          (indexTreeAux k half (by simp [half])))

/--
The canonical parity-order recursion tree of evaluation indices for a radix-2
domain.
-/
noncomputable def indexTree (domain : Radix2Domain F) : Radix2.FFTTree (Fin domain.size) :=
  indexTreeAux domain.logSize domain rfl

theorem indexTreeAux_zero (domain : Radix2Domain F) (hk : domain.logSize = 0) :
    indexTreeAux 0 domain hk = Radix2.FFTTree.leaf (Fin.mk 0 domain.size_pos) := by
  rfl

theorem indexTreeAux_succ (k : Nat) (domain : Radix2Domain F)
    (hk : domain.logSize = k + 1) :
    indexTreeAux (k + 1) domain hk =
      Radix2.FFTTree.node
        (Radix2.FFTTree.map (domain.evenIndex (by simp [hk]))
          (indexTreeAux k (domain.succHalf hk)
            (by simp)))
        (Radix2.FFTTree.map (domain.oddIndex (by simp [hk]))
          (indexTreeAux k (domain.succHalf hk)
            (by simp))) := by
  rfl

theorem leafCount_indexTreeAux :
    (k : Nat) ->
    (domain : Radix2Domain F) ->
    (hk : domain.logSize = k) ->
    (indexTreeAux k domain hk).leafCount = domain.size
  | 0, domain, hk => by
      have hsize : domain.size = 1 := by
        simpa [hk] using domain.size_eq_pow
      simp [indexTreeAux, hsize, Radix2.FFTTree.leafCount]
  | Nat.succ k, domain, hk => by
      let hpos : 0 < domain.logSize := by simp [hk]
      let half := domain.succHalf hk
      have hkHalf : half.logSize = k := by
        simp [half]
      have ihHalf : (indexTreeAux k half hkHalf).leafCount = half.size :=
        leafCount_indexTreeAux k half hkHalf
      have hstep :
          (indexTreeAux (k + 1) domain hk).leafCount =
            (indexTreeAux k half hkHalf).leafCount
              + (indexTreeAux k half hkHalf).leafCount := by
        simpa [hkHalf, Radix2.FFTTree.leafCount, Radix2.FFTTree.leafCount_map] using
          congrArg Radix2.FFTTree.leafCount (indexTreeAux_succ k domain hk)
      calc
        (indexTreeAux (k + 1) domain hk).leafCount
            = (indexTreeAux k half hkHalf).leafCount
              + (indexTreeAux k half hkHalf).leafCount := hstep
        _ = half.size + half.size := by
              simp [ihHalf]
        _ = domain.size := by
              simpa using (domain.size_eq_halfSize_add_halfSize hpos).symm

theorem leafCount_indexTree (domain : Radix2Domain F) :
    domain.indexTree.leafCount = domain.size := by
  simpa [indexTree] using leafCount_indexTreeAux domain.logSize domain rfl

theorem parityTreeAux_eq_map_transform_indexTreeAux :
    (k : Nat) ->
    (domain : Radix2Domain F) ->
    (hk : domain.logSize = k) ->
    (poly : Polynomial F) ->
    parityTreeAux k domain hk poly =
      Radix2.FFTTree.map (fun i => domain.toNTTSpec.transform poly i)
        (indexTreeAux k domain hk)
  | 0, domain, hk, poly => by
      rfl
  | Nat.succ k, domain, hk, poly => by
      let hpos : 0 < domain.logSize := by simp [hk]
      let half := domain.succHalf hk
      have hkHalf : half.logSize = k := by
        simp [half]
      have ihEven := parityTreeAux_eq_map_transform_indexTreeAux k half hkHalf poly
      have ihOdd := parityTreeAux_eq_map_transform_indexTreeAux k half hkHalf
        (domain.twistPolynomial poly)
      have hparity := parityTreeAux_succ k domain hk poly
      have hindex := indexTreeAux_succ k domain hk
      have hleft :
          (fun i => domain.toNTTSpec.transform poly (domain.evenIndex hpos i)) =
            half.toNTTSpec.transform poly := by
        funext i
        change poly.eval (domain.point (domain.evenIndex hpos i)) =
          poly.eval ((domain.halfDomain hpos).point i)
        rw [halfDomain_point_eq_evenPoint]
      have hright :
          (fun i => domain.toNTTSpec.transform poly (domain.oddIndex hpos i)) =
            half.toNTTSpec.transform (domain.twistPolynomial poly) := by
        funext i
        simpa [half, Radix2Domain.oddValues] using
          congrFun (oddValues_transform_eq_halfDomain_transform_twist domain hpos poly) i
      have hmapEven :
          Radix2.FFTTree.map (half.toNTTSpec.transform poly) (indexTreeAux k half hkHalf) =
            Radix2.FFTTree.map
              (Function.comp (fun i => domain.toNTTSpec.transform poly i) (domain.evenIndex hpos))
              (indexTreeAux k half hkHalf) :=
        Radix2.FFTTree.map_congr
          (fun i => by simpa [Function.comp] using (congrFun hleft i).symm)
          (indexTreeAux k half hkHalf)
      have hmapOdd :
          Radix2.FFTTree.map (half.toNTTSpec.transform (domain.twistPolynomial poly))
              (indexTreeAux k half hkHalf) =
            Radix2.FFTTree.map
              (Function.comp (fun i => domain.toNTTSpec.transform poly i) (domain.oddIndex hpos))
              (indexTreeAux k half hkHalf) :=
        Radix2.FFTTree.map_congr
          (fun i => by simpa [Function.comp] using (congrFun hright i).symm)
          (indexTreeAux k half hkHalf)
      have hcomposeEven :
          Radix2.FFTTree.map
              (Function.comp (fun i => domain.toNTTSpec.transform poly i) (domain.evenIndex hpos))
              (indexTreeAux k half hkHalf) =
            Radix2.FFTTree.map (fun i => domain.toNTTSpec.transform poly i)
              (Radix2.FFTTree.map (domain.evenIndex hpos) (indexTreeAux k half hkHalf)) := by
        simpa using
          (Radix2.FFTTree.map_map (fun i => domain.toNTTSpec.transform poly i)
            (domain.evenIndex hpos) (indexTreeAux k half hkHalf)).symm
      have hcomposeOdd :
          Radix2.FFTTree.map
              (Function.comp (fun i => domain.toNTTSpec.transform poly i) (domain.oddIndex hpos))
              (indexTreeAux k half hkHalf) =
            Radix2.FFTTree.map (fun i => domain.toNTTSpec.transform poly i)
              (Radix2.FFTTree.map (domain.oddIndex hpos) (indexTreeAux k half hkHalf)) := by
        simpa using
          (Radix2.FFTTree.map_map (fun i => domain.toNTTSpec.transform poly i)
            (domain.oddIndex hpos) (indexTreeAux k half hkHalf)).symm
      have hmapIndex :
          Radix2.FFTTree.map (fun i => domain.toNTTSpec.transform poly i) (indexTreeAux (k + 1) domain hk) =
            Radix2.FFTTree.node
              (Radix2.FFTTree.map (fun i => domain.toNTTSpec.transform poly i)
                (Radix2.FFTTree.map (domain.evenIndex hpos) (indexTreeAux k half hkHalf)))
              (Radix2.FFTTree.map (fun i => domain.toNTTSpec.transform poly i)
                (Radix2.FFTTree.map (domain.oddIndex hpos) (indexTreeAux k half hkHalf))) := by
        simpa [half, hkHalf, Radix2.FFTTree.map] using
          congrArg (Radix2.FFTTree.map (fun i => domain.toNTTSpec.transform poly i)) hindex
      calc
        parityTreeAux (k + 1) domain hk poly
            = Radix2.FFTTree.node
                (parityTreeAux k half hkHalf poly)
                (parityTreeAux k half hkHalf (domain.twistPolynomial poly)) := by
                  simpa [half, hkHalf] using hparity
        _ = Radix2.FFTTree.node
              (Radix2.FFTTree.map (half.toNTTSpec.transform poly)
                (indexTreeAux k half hkHalf))
              (Radix2.FFTTree.map (half.toNTTSpec.transform (domain.twistPolynomial poly))
                (indexTreeAux k half hkHalf)) := by
                  rw [ihEven, ihOdd]
        _ = Radix2.FFTTree.node
              (Radix2.FFTTree.map (Function.comp (fun i => domain.toNTTSpec.transform poly i)
                (domain.evenIndex hpos))
                (indexTreeAux k half hkHalf))
              (Radix2.FFTTree.map (Function.comp (fun i => domain.toNTTSpec.transform poly i)
                (domain.oddIndex hpos))
                (indexTreeAux k half hkHalf)) := by
                  rw [hmapEven, hmapOdd]
        _ = Radix2.FFTTree.node
              (Radix2.FFTTree.map (fun i => domain.toNTTSpec.transform poly i)
                (Radix2.FFTTree.map (domain.evenIndex hpos) (indexTreeAux k half hkHalf)))
              (Radix2.FFTTree.map (fun i => domain.toNTTSpec.transform poly i)
                (Radix2.FFTTree.map (domain.oddIndex hpos) (indexTreeAux k half hkHalf))) := by
                  rw [hcomposeEven, hcomposeOdd]
        _ = Radix2.FFTTree.map (fun i => domain.toNTTSpec.transform poly i)
              (indexTreeAux (k + 1) domain hk) := by
                simpa using hmapIndex.symm

theorem parityTree_eq_map_transform_indexTree (domain : Radix2Domain F)
    (poly : Polynomial F) :
    parityTree domain poly =
      Radix2.FFTTree.map (fun i => domain.toNTTSpec.transform poly i) domain.indexTree := by
  simpa [parityTree, indexTree] using
    parityTreeAux_eq_map_transform_indexTreeAux domain.logSize domain rfl poly

end Radix2Domain

end Zklib.Core
