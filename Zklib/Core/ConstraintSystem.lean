universe u v w x

namespace Zklib.Core

/--
A deliberately small but explicit interface for constraint-system semantics.

This layer is meant to host reusable meaning-level statements that multiple
frontends can target. The extra `System` and `PublicInput` boundary keeps the
spec honest about where statement generation ends and witness satisfaction
begins.
-/
structure ConstraintSystemSpec where
  System : Type u
  PublicInput : Type v
  Witness : Type w
  Statement : Type x
  statementOf : System -> PublicInput -> Statement
  satisfies : System -> PublicInput -> Witness -> Prop

namespace ConstraintSystemSpec

/--
View satisfaction as a relation over already-formed statements.
-/
def realizesStatement (spec : ConstraintSystemSpec)
    (system : spec.System) (statement : spec.Statement) (witness : spec.Witness) : Prop :=
  ∃ publicInput,
    spec.statementOf system publicInput = statement ∧
      spec.satisfies system publicInput witness

theorem realizesStatement_of_satisfies (spec : ConstraintSystemSpec)
    (system : spec.System) (publicInput : spec.PublicInput) (witness : spec.Witness)
    (hsat : spec.satisfies system publicInput witness) :
    spec.realizesStatement system (spec.statementOf system publicInput) witness := by
  exact ⟨publicInput, rfl, hsat⟩

end ConstraintSystemSpec

end Zklib.Core
