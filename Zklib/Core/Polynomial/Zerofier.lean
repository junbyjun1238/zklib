import Zklib.Core.Polynomial.Eval

universe u v

namespace Zklib.Core

/--
A zerofier package records a distinguished polynomial that vanishes on every
point of a chosen evaluation domain.

Keeping this separate from `PolynomialSpec` lets us stabilize evaluation-level
interfaces first, then add stronger algebraic structure only where needed.
-/
structure ZerofierSpec (F : Type u) [Monoid F] [Zero F] where
  toPolynomialSpec : PolynomialSpec.{u, v} F
  zerofier : EvaluationDomain F -> toPolynomialSpec.Carrier
  zerofier_vanishes :
    forall domain, toPolynomialSpec.vanishesOn (zerofier domain) domain

namespace ZerofierSpec

variable {F : Type u} [Monoid F] [Zero F]

theorem zerofier_eval_eq_zero (spec : ZerofierSpec F) (domain : EvaluationDomain F)
    (i : Fin domain.size) :
    spec.toPolynomialSpec.eval (spec.zerofier domain) (domain.point i) = 0 := by
  exact spec.zerofier_vanishes domain i

theorem zerofier_evaluations_eq_zero (spec : ZerofierSpec F)
    (domain : EvaluationDomain F) :
    spec.toPolynomialSpec.evaluations (spec.zerofier domain) domain = fun _ => 0 := by
  exact
    (PolynomialSpec.vanishesOn_iff_evaluations_eq_zero spec.toPolynomialSpec
      (spec.zerofier domain) domain).mp (spec.zerofier_vanishes domain)

end ZerofierSpec

end Zklib.Core
