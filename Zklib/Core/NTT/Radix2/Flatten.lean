import Zklib.Core.NTT.Radix2.IndexTree

namespace Zklib.Core

namespace Radix2Domain

variable {F : Type*} [Field F]

/--
The parity-order list of evaluation indices induced by the radix-2 recursion.
-/
noncomputable def indexOrder (domain : Radix2Domain F) : List (Fin domain.size) :=
  domain.indexTree.flatten

/--
The parity-order list of transform values produced by recursively visiting even
branches before odd branches.
-/
noncomputable def valuesInParityOrder (domain : Radix2Domain F) (poly : Polynomial F) : List F :=
  (parityTree domain poly).flatten

theorem length_indexOrder (domain : Radix2Domain F) :
    domain.indexOrder.length = domain.size := by
  simpa [indexOrder] using
    Eq.trans (Radix2.FFTTree.flatten_length domain.indexTree) (leafCount_indexTree domain)

theorem valuesInParityOrder_eq_map_transform_indexOrder (domain : Radix2Domain F)
    (poly : Polynomial F) :
    domain.valuesInParityOrder poly =
      domain.indexOrder.map (fun i => domain.toNTTSpec.transform poly i) := by
  calc
    domain.valuesInParityOrder poly
        = (Radix2.FFTTree.map (fun i => domain.toNTTSpec.transform poly i) domain.indexTree).flatten := by
            simp [valuesInParityOrder, parityTree_eq_map_transform_indexTree]
    _ = domain.indexOrder.map (fun i => domain.toNTTSpec.transform poly i) := by
          simpa [indexOrder] using
            Radix2.FFTTree.flatten_map (fun i => domain.toNTTSpec.transform poly i) domain.indexTree

theorem length_valuesInParityOrder (domain : Radix2Domain F) (poly : Polynomial F) :
    (domain.valuesInParityOrder poly).length = domain.size := by
  rw [valuesInParityOrder_eq_map_transform_indexOrder]
  simpa using length_indexOrder domain

end Radix2Domain

end Zklib.Core
