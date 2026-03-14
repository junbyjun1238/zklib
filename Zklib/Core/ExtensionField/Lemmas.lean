import Zklib.Core.ExtensionField.Basic

namespace Zklib.Core

namespace ExtensionAlgebraLaws

theorem add_zero (spec : ExtensionAlgebraLaws) (a : spec.Carrier) :
    spec.add a spec.zero = a := by
  calc
    spec.add a spec.zero = spec.add spec.zero a := spec.add_comm a spec.zero
    _ = a := spec.zero_add a

theorem add_right_neg (spec : ExtensionAlgebraLaws) (a : spec.Carrier) :
    spec.add a (spec.neg a) = spec.zero := by
  calc
    spec.add a (spec.neg a) = spec.add (spec.neg a) a := spec.add_comm a (spec.neg a)
    _ = spec.zero := spec.neg_add_cancel a

theorem mul_one (spec : ExtensionAlgebraLaws) (a : spec.Carrier) :
    spec.mul a spec.one = a := by
  calc
    spec.mul a spec.one = spec.mul spec.one a := spec.mul_comm a spec.one
    _ = a := spec.one_mul a

theorem right_distrib (spec : ExtensionAlgebraLaws) (a b c : spec.Carrier) :
    spec.mul (spec.add a b) c = spec.add (spec.mul a c) (spec.mul b c) := by
  calc
    spec.mul (spec.add a b) c = spec.mul c (spec.add a b) := spec.mul_comm (spec.add a b) c
    _ = spec.add (spec.mul c a) (spec.mul c b) := spec.left_distrib c a b
    _ = spec.add (spec.mul a c) (spec.mul b c) := by
      rw [spec.mul_comm c a, spec.mul_comm c b]

theorem add_left_cancel (spec : ExtensionAlgebraLaws) {a b c : spec.Carrier}
    (h : spec.add a b = spec.add a c) : b = c := by
  calc
    b = spec.add spec.zero b := by symm; exact spec.zero_add b
    _ = spec.add (spec.add (spec.neg a) a) b := by rw [spec.neg_add_cancel a]
    _ = spec.add (spec.neg a) (spec.add a b) := by rw [spec.add_assoc]
    _ = spec.add (spec.neg a) (spec.add a c) := by rw [h]
    _ = spec.add (spec.add (spec.neg a) a) c := by rw [(spec.add_assoc (spec.neg a) a c).symm]
    _ = spec.add spec.zero c := by rw [spec.neg_add_cancel a]
    _ = c := spec.zero_add c

theorem add_right_cancel (spec : ExtensionAlgebraLaws) {a b c : spec.Carrier}
    (h : spec.add b a = spec.add c a) : b = c := by
  apply spec.add_left_cancel
  calc
    spec.add a b = spec.add b a := spec.add_comm a b
    _ = spec.add c a := h
    _ = spec.add a c := spec.add_comm c a

end ExtensionAlgebraLaws

end Zklib.Core
