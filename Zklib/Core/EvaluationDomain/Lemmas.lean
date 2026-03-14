import Zklib.Core.EvaluationDomain.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

namespace Zklib.Core

namespace EvaluationDomain

variable {F : Type*} [Monoid F]

theorem point_eq_generator_pow (domain : EvaluationDomain F) (i : Fin domain.size) :
    domain.point i = domain.generator ^ (i : Nat) := by
  rfl

theorem point_injective (domain : EvaluationDomain F) :
    Function.Injective domain.point := by
  simpa [point] using domain.generator_pow_injective

theorem point_zero_eq_one (domain : EvaluationDomain F) :
    domain.point (Fin.mk 0 domain.size_pos) = 1 := by
  simp [point]

theorem point_succ (domain : EvaluationDomain F) (i : Fin domain.size)
    (h : i.1 + 1 < domain.size) :
    domain.point (Fin.mk (i.1 + 1) h) = domain.point i * domain.generator := by
  simpa [point] using (pow_succ domain.generator i.1)

theorem point_injOn_univ (domain : EvaluationDomain F) :
    Set.InjOn domain.point (↑(Finset.univ : Finset (Fin domain.size)) : Set (Fin domain.size)) := by
  intro i _ j _ hij
  exact domain.point_injective hij

end EvaluationDomain

namespace CosetEvaluationDomain

variable {F : Type*} [Monoid F]

theorem point_eq_shift_mul (domain : CosetEvaluationDomain F) (i : Fin domain.base.size) :
    domain.point i = domain.shift * domain.base.point i := by
  rfl

theorem point_zero_eq_shift (domain : CosetEvaluationDomain F) :
    domain.point (Fin.mk 0 domain.base.size_pos) = domain.shift := by
  simp [CosetEvaluationDomain.point, domain.base.point_zero_eq_one]

theorem point_succ (domain : CosetEvaluationDomain F) (i : Fin domain.base.size)
    (h : i.1 + 1 < domain.base.size) :
    domain.point (Fin.mk (i.1 + 1) h) = domain.point i * domain.base.generator := by
  calc
    domain.point (Fin.mk (i.1 + 1) h)
        = domain.shift * domain.base.point (Fin.mk (i.1 + 1) h) := rfl
    _ = domain.shift * (domain.base.point i * domain.base.generator) := by
      rw [domain.base.point_succ i h]
    _ = (domain.shift * domain.base.point i) * domain.base.generator := by
      rw [mul_assoc]
    _ = domain.point i * domain.base.generator := rfl

theorem ofBase_point_eq (domain : EvaluationDomain F) (i : Fin domain.size) :
    (CosetEvaluationDomain.ofBase domain).point i = domain.point i := by
  simp [CosetEvaluationDomain.ofBase, CosetEvaluationDomain.point]

theorem point_injective (domain : CosetEvaluationDomain F) :
    Function.Injective domain.point := by
  simpa [CosetEvaluationDomain.point] using domain.shift_point_injective

theorem point_injOn_univ (domain : CosetEvaluationDomain F) :
    Set.InjOn domain.point (↑(Finset.univ : Finset (Fin domain.base.size)) : Set (Fin domain.base.size)) := by
  intro i _ j _ hij
  exact domain.point_injective hij

end CosetEvaluationDomain

end Zklib.Core

