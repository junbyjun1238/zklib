import Zklib.Core.Field.Basic

universe u

namespace Zklib.Core

section

variable {R : Type u} [CommRing R]

theorem add_right_neg_eq_zero (a : R) : a + -a = 0 := by
  simp

theorem add_left_cancel_iff {a b c : R} : a + b = a + c ↔ b = c := by
  constructor
  · intro h
    exact add_left_cancel h
  · intro h
    simp [h]

theorem add_right_cancel_iff {a b c : R} : b + a = c + a ↔ b = c := by
  constructor
  · intro h
    exact add_right_cancel h
  · intro h
    simp [h]

end

end Zklib.Core
