import Zklib.Core.Subgroup.Basic
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

end Zklib.Core
