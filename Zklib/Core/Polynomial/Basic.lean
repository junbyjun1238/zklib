import Zklib.Core.Subgroup.Basic

namespace Zklib.Core

/--
A minimal polynomial specification over a coefficient carrier.

This is intentionally representation-agnostic so the project can decide later
whether dense, sparse, or quotient-based encodings deserve separate layers.
-/
structure PolynomialSpec (Coeff : Type*) where
  Carrier : Type*
  eval : Carrier -> Coeff -> Coeff

namespace PolynomialSpec

variable {F : Type*} [Monoid F]

/--
The evaluations of a polynomial over a fixed evaluation domain.
-/
def evaluations (spec : PolynomialSpec F) (poly : spec.Carrier)
    (domain : EvaluationDomain F) : Fin domain.size -> F :=
  fun i => spec.eval poly (domain.point i)

/--
Two polynomials agree on a domain when all indexed evaluation points match.
-/
def sameOn (spec : PolynomialSpec F) (p q : spec.Carrier)
    (domain : EvaluationDomain F) : Prop :=
  forall i, spec.eval p (domain.point i) = spec.eval q (domain.point i)

/--
A polynomial vanishes on a domain when all indexed evaluation points are zero.
-/
def vanishesOn [Zero F] (spec : PolynomialSpec F) (poly : spec.Carrier)
    (domain : EvaluationDomain F) : Prop :=
  forall i, spec.eval poly (domain.point i) = 0

end PolynomialSpec

end Zklib.Core
