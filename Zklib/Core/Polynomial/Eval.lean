import Zklib.Core.Polynomial.Basic

namespace Zklib.Core

namespace PolynomialSpec

variable {F : Type*} [Monoid F]

theorem sameOn_refl (spec : PolynomialSpec F) (p : spec.Carrier)
    (domain : EvaluationDomain F) :
    spec.sameOn p p domain := by
  intro i
  rfl

theorem sameOn_symm (spec : PolynomialSpec F) {p q : spec.Carrier}
    {domain : EvaluationDomain F} :
    spec.sameOn p q domain -> spec.sameOn q p domain := by
  intro h i
  symm
  exact h i

theorem sameOn_trans (spec : PolynomialSpec F) {p q r : spec.Carrier}
    {domain : EvaluationDomain F} :
    spec.sameOn p q domain -> spec.sameOn q r domain -> spec.sameOn p r domain := by
  intro hpq hqr i
  trans spec.eval q (domain.point i)
  exact hpq i
  exact hqr i

theorem sameOn_iff_evaluations_eq (spec : PolynomialSpec F) (p q : spec.Carrier)
    (domain : EvaluationDomain F) :
    spec.sameOn p q domain <-> spec.evaluations p domain = spec.evaluations q domain := by
  constructor
  · intro h
    funext i
    exact h i
  · intro h i
    exact congrFun h i

theorem vanishesOn_iff_evaluations_eq_zero [Zero F] (spec : PolynomialSpec F)
    (poly : spec.Carrier) (domain : EvaluationDomain F) :
    spec.vanishesOn poly domain <-> spec.evaluations poly domain = fun _ => 0 := by
  constructor
  · intro h
    funext i
    exact h i
  · intro h i
    exact congrFun h i

end PolynomialSpec

end Zklib.Core
