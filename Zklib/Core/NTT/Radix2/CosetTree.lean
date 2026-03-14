import Zklib.Core.NTT.Radix2.CosetCorrectness
import Zklib.Core.NTT.Radix2.IndexTree

namespace Zklib.Core

namespace CosetRadix2Domain

variable {F : Type*} [Field F]

/--
Auxiliary recursion tree for parity-split coset FFT development.

The parameter `k` tracks the expected radix-2 depth, and the equality witness
ties that depth to the base domain's `logSize`.
-/
noncomputable def parityTreeAux :
    (k : Nat) ->
    (domain : CosetRadix2Domain F) ->
    domain.base.logSize = k ->
    Polynomial F ->
    Radix2.FFTTree F
  | 0, domain, hk, poly =>
      Radix2.FFTTree.leaf (domain.toCosetNTTSpec.transform poly (Fin.mk 0 domain.base.size_pos))
  | Nat.succ k, domain, hk, poly =>
      let hpos : 0 < domain.base.logSize := by simp [hk]
      let evenDom := domain.succHalfEven hk
      let oddDom := domain.succHalfOdd hk
      Radix2.FFTTree.node
        (parityTreeAux k evenDom
          (by simp [evenDom]) poly)
        (parityTreeAux k oddDom
          (by simp [oddDom]) poly)

/--
The recursive radix-2 parity-split decomposition tree of a coset transform.
-/
noncomputable def parityTree (domain : CosetRadix2Domain F) (poly : Polynomial F) :
    Radix2.FFTTree F :=
  parityTreeAux domain.base.logSize domain rfl poly

theorem parityTreeAux_zero (domain : CosetRadix2Domain F) (hk : domain.base.logSize = 0)
    (poly : Polynomial F) :
    parityTreeAux 0 domain hk poly =
      Radix2.FFTTree.leaf (domain.toCosetNTTSpec.transform poly (Fin.mk 0 domain.base.size_pos)) := by
  rfl

theorem parityTreeAux_succ (k : Nat) (domain : CosetRadix2Domain F)
    (hk : domain.base.logSize = k + 1) (poly : Polynomial F) :
    parityTreeAux (k + 1) domain hk poly =
      Radix2.FFTTree.node
        (parityTreeAux k (domain.succHalfEven hk)
          (by simp) poly)
        (parityTreeAux k (domain.succHalfOdd hk)
          (by simp) poly) := by
  rfl

theorem parityTreeAux_eq_map_transform_indexTreeAux :
    (k : Nat) ->
    (domain : CosetRadix2Domain F) ->
    (hk : domain.base.logSize = k) ->
    (poly : Polynomial F) ->
    parityTreeAux k domain hk poly =
      Radix2.FFTTree.map (fun i => domain.toCosetNTTSpec.transform poly i)
        (Radix2Domain.indexTreeAux k domain.base hk)
  | 0, domain, hk, poly => by
      rfl
  | Nat.succ k, domain, hk, poly => by
      let hpos : 0 < domain.base.logSize := by simp [hk]
      let evenDom := domain.succHalfEven hk
      let oddDom := domain.succHalfOdd hk
      have hkEven : evenDom.base.logSize = k := by
        simp [evenDom]
      have hkOdd : oddDom.base.logSize = k := by
        simp [oddDom]
      have ihEven := parityTreeAux_eq_map_transform_indexTreeAux k evenDom hkEven poly
      have ihOdd := parityTreeAux_eq_map_transform_indexTreeAux k oddDom hkOdd poly
      have hparity := parityTreeAux_succ k domain hk poly
      have hindex := Radix2Domain.indexTreeAux_succ k domain.base hk
      have hleft :
          (fun i => domain.toCosetNTTSpec.transform poly (domain.base.evenIndex hpos i)) =
            evenDom.toCosetNTTSpec.transform poly := by
        funext i
        exact transform_evenIndex_eq domain hpos poly i
      have hright :
          (fun i => domain.toCosetNTTSpec.transform poly (domain.base.oddIndex hpos i)) =
            oddDom.toCosetNTTSpec.transform poly := by
        funext i
        exact transform_oddIndex_eq domain hpos poly i
      have hmapEven :
          Radix2.FFTTree.map (evenDom.toCosetNTTSpec.transform poly)
              (Radix2Domain.indexTreeAux k evenDom.base hkEven) =
            Radix2.FFTTree.map
              (Function.comp (fun i => domain.toCosetNTTSpec.transform poly i)
                (domain.base.evenIndex hpos))
              (Radix2Domain.indexTreeAux k evenDom.base hkEven) :=
        Radix2.FFTTree.map_congr
          (fun i => by simpa [Function.comp] using (congrFun hleft i).symm)
          (Radix2Domain.indexTreeAux k evenDom.base hkEven)
      have hmapOdd :
          Radix2.FFTTree.map (oddDom.toCosetNTTSpec.transform poly)
              (Radix2Domain.indexTreeAux k oddDom.base hkOdd) =
            Radix2.FFTTree.map
              (Function.comp (fun i => domain.toCosetNTTSpec.transform poly i)
                (domain.base.oddIndex hpos))
              (Radix2Domain.indexTreeAux k oddDom.base hkOdd) :=
        Radix2.FFTTree.map_congr
          (fun i => by simpa [Function.comp] using (congrFun hright i).symm)
          (Radix2Domain.indexTreeAux k oddDom.base hkOdd)
      have hcomposeEven :
          Radix2.FFTTree.map
              (Function.comp (fun i => domain.toCosetNTTSpec.transform poly i)
                (domain.base.evenIndex hpos))
              (Radix2Domain.indexTreeAux k evenDom.base hkEven) =
            Radix2.FFTTree.map (fun i => domain.toCosetNTTSpec.transform poly i)
              (Radix2.FFTTree.map (domain.base.evenIndex hpos)
                (Radix2Domain.indexTreeAux k evenDom.base hkEven)) := by
        simpa using
          (Radix2.FFTTree.map_map (fun i => domain.toCosetNTTSpec.transform poly i)
            (domain.base.evenIndex hpos) (Radix2Domain.indexTreeAux k evenDom.base hkEven)).symm
      have hcomposeOdd :
          Radix2.FFTTree.map
              (Function.comp (fun i => domain.toCosetNTTSpec.transform poly i)
                (domain.base.oddIndex hpos))
              (Radix2Domain.indexTreeAux k oddDom.base hkOdd) =
            Radix2.FFTTree.map (fun i => domain.toCosetNTTSpec.transform poly i)
              (Radix2.FFTTree.map (domain.base.oddIndex hpos)
                (Radix2Domain.indexTreeAux k oddDom.base hkOdd)) := by
        simpa using
          (Radix2.FFTTree.map_map (fun i => domain.toCosetNTTSpec.transform poly i)
            (domain.base.oddIndex hpos) (Radix2Domain.indexTreeAux k oddDom.base hkOdd)).symm
      have hmapIndex :
          Radix2.FFTTree.map (fun i => domain.toCosetNTTSpec.transform poly i)
              (Radix2Domain.indexTreeAux (k + 1) domain.base hk) =
            Radix2.FFTTree.node
              (Radix2.FFTTree.map (fun i => domain.toCosetNTTSpec.transform poly i)
                (Radix2.FFTTree.map (domain.base.evenIndex hpos)
                  (Radix2Domain.indexTreeAux k evenDom.base hkEven)))
              (Radix2.FFTTree.map (fun i => domain.toCosetNTTSpec.transform poly i)
                (Radix2.FFTTree.map (domain.base.oddIndex hpos)
                  (Radix2Domain.indexTreeAux k oddDom.base hkOdd))) := by
        simpa [evenDom, oddDom, hkEven, hkOdd, Radix2.FFTTree.map] using
          congrArg (Radix2.FFTTree.map (fun i => domain.toCosetNTTSpec.transform poly i)) hindex
      calc
        parityTreeAux (k + 1) domain hk poly
            = Radix2.FFTTree.node
                (parityTreeAux k evenDom hkEven poly)
                (parityTreeAux k oddDom hkOdd poly) := by
                  simpa [evenDom, oddDom, hkEven, hkOdd] using hparity
        _ = Radix2.FFTTree.node
              (Radix2.FFTTree.map (evenDom.toCosetNTTSpec.transform poly)
                (Radix2Domain.indexTreeAux k evenDom.base hkEven))
              (Radix2.FFTTree.map (oddDom.toCosetNTTSpec.transform poly)
                (Radix2Domain.indexTreeAux k oddDom.base hkOdd)) := by
                  rw [ihEven, ihOdd]
        _ = Radix2.FFTTree.node
              (Radix2.FFTTree.map
                (Function.comp (fun i => domain.toCosetNTTSpec.transform poly i)
                  (domain.base.evenIndex hpos))
                (Radix2Domain.indexTreeAux k evenDom.base hkEven))
              (Radix2.FFTTree.map
                (Function.comp (fun i => domain.toCosetNTTSpec.transform poly i)
                  (domain.base.oddIndex hpos))
                (Radix2Domain.indexTreeAux k oddDom.base hkOdd)) := by
                  rw [hmapEven, hmapOdd]
        _ = Radix2.FFTTree.node
              (Radix2.FFTTree.map (fun i => domain.toCosetNTTSpec.transform poly i)
                (Radix2.FFTTree.map (domain.base.evenIndex hpos)
                  (Radix2Domain.indexTreeAux k evenDom.base hkEven)))
              (Radix2.FFTTree.map (fun i => domain.toCosetNTTSpec.transform poly i)
                (Radix2.FFTTree.map (domain.base.oddIndex hpos)
                  (Radix2Domain.indexTreeAux k oddDom.base hkOdd))) := by
                  rw [hcomposeEven, hcomposeOdd]
        _ = Radix2.FFTTree.map (fun i => domain.toCosetNTTSpec.transform poly i)
              (Radix2Domain.indexTreeAux (k + 1) domain.base hk) := by
                simpa using hmapIndex.symm

theorem parityTree_eq_map_transform_indexTree (domain : CosetRadix2Domain F)
    (poly : Polynomial F) :
    parityTree domain poly =
      Radix2.FFTTree.map (fun i => domain.toCosetNTTSpec.transform poly i) domain.base.indexTree := by
  simpa [parityTree, Radix2Domain.indexTree] using
    parityTreeAux_eq_map_transform_indexTreeAux domain.base.logSize domain rfl poly

end CosetRadix2Domain

end Zklib.Core
