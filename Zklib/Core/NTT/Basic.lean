import Zklib.Core.Polynomial.Lagrange

universe u v

namespace Zklib.Core

/--
An NTT package is an evaluation domain together with a canonical interpolation
procedure for polynomials over that domain.

At this layer, "forward transform" means domain evaluation and "inverse
transform" means the chosen canonical interpolant. Later files can add
algorithmic refinements without changing these semantics.
-/
structure NTTSpec (F : Type u) [Monoid F] where
  toInterpolationSpec : InterpolationSpec.{u, v} F
  domain : EvaluationDomain F

namespace NTTSpec

variable {F : Type u} [Monoid F]

/--
The underlying polynomial specification seen by the transform.
-/
def toPolynomialSpec (spec : NTTSpec F) : PolynomialSpec F :=
  spec.toInterpolationSpec.toPolynomialSpec

/--
The forward transform is evaluation on the chosen domain.
-/
def transform (spec : NTTSpec F) (poly : spec.toPolynomialSpec.Carrier) :
    Fin spec.domain.size -> F :=
  spec.toPolynomialSpec.evaluations poly spec.domain

/--
The inverse transform is the canonical interpolant for a domain value table.
-/
def inverse (spec : NTTSpec F) (values : Fin spec.domain.size -> F) :
    spec.toPolynomialSpec.Carrier :=
  spec.toInterpolationSpec.interpolate spec.domain values

/--
Build an NTT package from any interpolation package and evaluation domain.
-/
def ofInterpolation (interp : InterpolationSpec.{u, v} F)
    (domain : EvaluationDomain F) : NTTSpec F where
  toInterpolationSpec := interp
  domain := domain

end NTTSpec

namespace NTTSpec

variable {F : Type*} [Field F]

/--
Concrete NTT semantics backed by `mathlib` polynomials and Lagrange
interpolation.
-/
noncomputable def mathlib (domain : EvaluationDomain F) : NTTSpec F :=
  ofInterpolation (InterpolationSpec.mathlib F) domain

end NTTSpec

end Zklib.Core
