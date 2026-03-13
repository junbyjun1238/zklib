import Zklib.Core.NTT.Basic

universe u v

namespace Zklib.Core

namespace NTTSpec

variable {F : Type u} [Monoid F]

theorem transform_eq_evaluations (spec : NTTSpec F)
    (poly : spec.toPolynomialSpec.Carrier) :
    spec.transform poly = spec.toPolynomialSpec.evaluations poly spec.domain := by
  rfl

theorem inverse_spec (spec : NTTSpec F) (values : Fin spec.domain.size -> F) :
    spec.toPolynomialSpec.InterpolatesOn spec.domain values (spec.inverse values) := by
  exact spec.toInterpolationSpec.interpolate_spec spec.domain values

theorem transform_inverse (spec : NTTSpec F) (values : Fin spec.domain.size -> F) :
    spec.transform (spec.inverse values) = values := by
  simpa [transform] using
    (PolynomialSpec.interpolatesOn_iff_evaluations_eq spec.toPolynomialSpec
      spec.domain values (spec.inverse values)).mp (spec.inverse_spec values)

theorem inverse_transform_sameOn (spec : NTTSpec F)
    (poly : spec.toPolynomialSpec.Carrier) :
    spec.toPolynomialSpec.sameOn (spec.inverse (spec.transform poly)) poly spec.domain := by
  apply PolynomialSpec.interpolatesOn_unique_up_to_sameOn spec.toPolynomialSpec
  · exact spec.inverse_spec (spec.transform poly)
  · intro i
    rfl

end NTTSpec

namespace NTTSpec

variable {F : Type*} [Field F]

theorem inverse_transform_eq_of_degree_lt (domain : EvaluationDomain F)
    {poly : Polynomial F} (hdeg : poly.degree < domain.size) :
    (mathlib domain).inverse ((mathlib domain).transform poly) = poly := by
  change (InterpolationSpec.mathlib F).interpolate domain
      ((PolynomialSpec.mathlib F).evaluations poly domain) = poly
  simpa using (InterpolationSpec.eq_interpolate domain hdeg).symm

end NTTSpec

end Zklib.Core
