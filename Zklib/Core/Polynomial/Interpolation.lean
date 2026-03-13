import Zklib.Core.Polynomial.Eval

universe u v

namespace Zklib.Core

namespace PolynomialSpec

variable {F : Type*} [Monoid F]

/--
A polynomial interpolates a value table over a domain when its evaluations match
the table pointwise.
-/
def InterpolatesOn (spec : PolynomialSpec F) (domain : EvaluationDomain F)
    (values : Fin domain.size -> F) (poly : spec.Carrier) : Prop :=
  forall i, spec.eval poly (domain.point i) = values i

/--
A polynomial interpolates a value table over a coset domain when its shifted
evaluations match the table pointwise.
-/
def InterpolatesOnCoset (spec : PolynomialSpec F) (domain : CosetEvaluationDomain F)
    (values : Fin domain.base.size -> F) (poly : spec.Carrier) : Prop :=
  forall i, spec.eval poly (domain.point i) = values i

theorem interpolatesOn_iff_evaluations_eq (spec : PolynomialSpec F)
    (domain : EvaluationDomain F) (values : Fin domain.size -> F) (poly : spec.Carrier) :
    spec.InterpolatesOn domain values poly <-> spec.evaluations poly domain = values := by
  constructor
  · intro h
    funext i
    exact h i
  · intro h i
    exact congrFun h i

theorem interpolatesOnCoset_iff_cosetEvaluations_eq (spec : PolynomialSpec F)
    (domain : CosetEvaluationDomain F) (values : Fin domain.base.size -> F) (poly : spec.Carrier) :
    spec.InterpolatesOnCoset domain values poly <->
      spec.cosetEvaluations poly domain = values := by
  constructor
  · intro h
    funext i
    exact h i
  · intro h i
    exact congrFun h i

theorem interpolatesOn_unique_up_to_sameOn (spec : PolynomialSpec F)
    {domain : EvaluationDomain F} {values : Fin domain.size -> F}
    {p q : spec.Carrier} :
    spec.InterpolatesOn domain values p ->
    spec.InterpolatesOn domain values q ->
    spec.sameOn p q domain := by
  intro hp hq i
  calc
    spec.eval p (domain.point i) = values i := hp i
    _ = spec.eval q (domain.point i) := (hq i).symm

theorem interpolatesOnCoset_unique_up_to_sameOnCoset (spec : PolynomialSpec F)
    {domain : CosetEvaluationDomain F} {values : Fin domain.base.size -> F}
    {p q : spec.Carrier} :
    spec.InterpolatesOnCoset domain values p ->
    spec.InterpolatesOnCoset domain values q ->
    spec.sameOnCoset p q domain := by
  intro hp hq i
  calc
    spec.eval p (domain.point i) = values i := hp i
    _ = spec.eval q (domain.point i) := (hq i).symm

end PolynomialSpec

/--
An interpolation package provides a canonical interpolant for any finite
evaluation domain and value table.

This captures the existence side constructively, while uniqueness is proved
later as agreement on the domain.
-/
structure InterpolationSpec (F : Type u) [Monoid F] where
  toPolynomialSpec : PolynomialSpec.{u, v} F
  interpolate :
    (domain : EvaluationDomain F) ->
    (Fin domain.size -> F) ->
    toPolynomialSpec.Carrier
  interpolate_spec :
    forall domain values,
      toPolynomialSpec.InterpolatesOn domain values (interpolate domain values)

namespace InterpolationSpec

variable {F : Type u} [Monoid F]

theorem exists_interpolant (spec : InterpolationSpec F)
    (domain : EvaluationDomain F) (values : Fin domain.size -> F) :
    ∃ poly, spec.toPolynomialSpec.InterpolatesOn domain values poly := by
  exact ⟨spec.interpolate domain values, spec.interpolate_spec domain values⟩

theorem interpolate_unique_up_to_sameOn (spec : InterpolationSpec F)
    {domain : EvaluationDomain F} {values : Fin domain.size -> F}
    {poly : spec.toPolynomialSpec.Carrier} :
    spec.toPolynomialSpec.InterpolatesOn domain values poly ->
    spec.toPolynomialSpec.sameOn poly (spec.interpolate domain values) domain := by
  intro hpoly
  exact
    PolynomialSpec.interpolatesOn_unique_up_to_sameOn spec.toPolynomialSpec
      hpoly (spec.interpolate_spec domain values)

theorem any_two_interpolants_agree (spec : InterpolationSpec F)
    {domain : EvaluationDomain F} {values : Fin domain.size -> F}
    {p q : spec.toPolynomialSpec.Carrier} :
    spec.toPolynomialSpec.InterpolatesOn domain values p ->
    spec.toPolynomialSpec.InterpolatesOn domain values q ->
    spec.toPolynomialSpec.sameOn p q domain := by
  exact PolynomialSpec.interpolatesOn_unique_up_to_sameOn spec.toPolynomialSpec

end InterpolationSpec

/--
A canonical interpolation package over shifted coset domains.
-/
structure CosetInterpolationSpec (F : Type u) [Monoid F] where
  toPolynomialSpec : PolynomialSpec.{u, v} F
  interpolate :
    (domain : CosetEvaluationDomain F) ->
    (Fin domain.base.size -> F) ->
    toPolynomialSpec.Carrier
  interpolate_spec :
    forall domain values,
      toPolynomialSpec.InterpolatesOnCoset domain values (interpolate domain values)

namespace CosetInterpolationSpec

variable {F : Type u} [Monoid F]

theorem exists_interpolant (spec : CosetInterpolationSpec F)
    (domain : CosetEvaluationDomain F) (values : Fin domain.base.size -> F) :
    ∃ poly, spec.toPolynomialSpec.InterpolatesOnCoset domain values poly := by
  exact ⟨spec.interpolate domain values, spec.interpolate_spec domain values⟩

theorem interpolate_unique_up_to_sameOnCoset (spec : CosetInterpolationSpec F)
    {domain : CosetEvaluationDomain F} {values : Fin domain.base.size -> F}
    {poly : spec.toPolynomialSpec.Carrier} :
    spec.toPolynomialSpec.InterpolatesOnCoset domain values poly ->
    spec.toPolynomialSpec.sameOnCoset poly (spec.interpolate domain values) domain := by
  intro hpoly
  exact
    PolynomialSpec.interpolatesOnCoset_unique_up_to_sameOnCoset spec.toPolynomialSpec
      hpoly (spec.interpolate_spec domain values)

theorem any_two_interpolants_agree (spec : CosetInterpolationSpec F)
    {domain : CosetEvaluationDomain F} {values : Fin domain.base.size -> F}
    {p q : spec.toPolynomialSpec.Carrier} :
    spec.toPolynomialSpec.InterpolatesOnCoset domain values p ->
    spec.toPolynomialSpec.InterpolatesOnCoset domain values q ->
    spec.toPolynomialSpec.sameOnCoset p q domain := by
  exact PolynomialSpec.interpolatesOnCoset_unique_up_to_sameOnCoset spec.toPolynomialSpec

end CosetInterpolationSpec

end Zklib.Core
