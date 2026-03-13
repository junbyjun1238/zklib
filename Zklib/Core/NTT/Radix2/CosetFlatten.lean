import Zklib.Core.NTT.Radix2.CosetTree
import Zklib.Core.NTT.Radix2.BitReversal

namespace Zklib.Core

namespace CosetRadix2Domain

variable {F : Type*} [Field F]

/--
The parity-order list of evaluation indices induced by the coset radix-2
recursion. The visited indices are inherited from the base radix-2 domain.
-/
noncomputable def indexOrder (domain : CosetRadix2Domain F) : List (Fin domain.base.size) :=
  domain.base.indexOrder

/--
The canonical bit-reversal ordering for a coset radix-2 domain, inherited from
its base domain.
-/
noncomputable def bitRevOrder (domain : CosetRadix2Domain F) : List (Fin domain.base.size) :=
  domain.base.bitRevOrder

/--
The explicit function-enumerated bit-reversal ordering for a coset radix-2
domain.
-/
noncomputable def bitRevOrderFn (domain : CosetRadix2Domain F) : List (Fin domain.base.size) :=
  domain.base.bitRevOrderFn

/--
The parity-order list of transform values produced by recursively visiting
even branches before odd branches.
-/
noncomputable def valuesInParityOrder (domain : CosetRadix2Domain F) (poly : Polynomial F) :
    List F :=
  (parityTree domain poly).flatten

theorem length_indexOrder (domain : CosetRadix2Domain F) :
    domain.indexOrder.length = domain.base.size := by
  simpa [indexOrder] using domain.base.length_indexOrder

theorem bitRevOrder_eq_indexOrder (domain : CosetRadix2Domain F) :
    domain.bitRevOrder = domain.indexOrder := by
  simpa [bitRevOrder, indexOrder] using domain.base.bitRevOrder_eq_indexOrder

theorem bitRevOrderFn_eq_bitRevOrder (domain : CosetRadix2Domain F) :
    domain.bitRevOrderFn = domain.bitRevOrder := by
  simpa [bitRevOrderFn, bitRevOrder] using domain.base.bitRevOrderFn_eq_bitRevOrder

theorem valuesInParityOrder_eq_map_transform_indexOrder (domain : CosetRadix2Domain F)
    (poly : Polynomial F) :
    domain.valuesInParityOrder poly =
      domain.indexOrder.map (fun i => domain.toCosetNTTSpec.transform poly i) := by
  calc
    domain.valuesInParityOrder poly
        = (Radix2.FFTTree.map (fun i => domain.toCosetNTTSpec.transform poly i)
            domain.base.indexTree).flatten := by
              simp [valuesInParityOrder, parityTree_eq_map_transform_indexTree]
    _ = domain.indexOrder.map (fun i => domain.toCosetNTTSpec.transform poly i) := by
          simpa [indexOrder] using
            Radix2.FFTTree.flatten_map (fun i => domain.toCosetNTTSpec.transform poly i)
              domain.base.indexTree

theorem valuesInParityOrder_eq_map_transform_bitRevOrder (domain : CosetRadix2Domain F)
    (poly : Polynomial F) :
    domain.valuesInParityOrder poly =
      domain.bitRevOrder.map (fun i => domain.toCosetNTTSpec.transform poly i) := by
  rw [domain.bitRevOrder_eq_indexOrder]
  exact valuesInParityOrder_eq_map_transform_indexOrder domain poly

theorem valuesInParityOrder_eq_map_transform_bitRevOrderFn (domain : CosetRadix2Domain F)
    (poly : Polynomial F) :
    domain.valuesInParityOrder poly =
      domain.bitRevOrderFn.map (fun i => domain.toCosetNTTSpec.transform poly i) := by
  rw [domain.bitRevOrderFn_eq_bitRevOrder]
  exact valuesInParityOrder_eq_map_transform_bitRevOrder domain poly

theorem length_valuesInParityOrder (domain : CosetRadix2Domain F) (poly : Polynomial F) :
    (domain.valuesInParityOrder poly).length = domain.base.size := by
  rw [valuesInParityOrder_eq_map_transform_indexOrder]
  simpa using length_indexOrder domain

end CosetRadix2Domain

end Zklib.Core
