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
  publicInputOf? : System -> Statement -> Option PublicInput
  publicInputOf?_statementOf :
    ∀ system publicInput,
      publicInputOf? system (statementOf system publicInput) = some publicInput
  satisfies : System -> PublicInput -> Witness -> Prop

namespace ConstraintSystemSpec

/--
Recover the canonical public input associated with an already-formed statement,
when the statement is well-formed for the chosen system.
-/
def canonicalPublicInput? (spec : ConstraintSystemSpec)
    (system : spec.System) (statement : spec.Statement) : Option spec.PublicInput :=
  spec.publicInputOf? system statement

/--
View statement formation as a well-formedness predicate over statements.
-/
def WellFormedStatement (spec : ConstraintSystemSpec)
    (system : spec.System) (statement : spec.Statement) : Prop :=
  ∃ publicInput, spec.publicInputOf? system statement = some publicInput

/--
View satisfaction as a relation over already-formed statements.
-/
def realizesStatement (spec : ConstraintSystemSpec)
    (system : spec.System) (statement : spec.Statement) (witness : spec.Witness) : Prop :=
  ∃ publicInput,
    spec.publicInputOf? system statement = some publicInput ∧
      spec.satisfies system publicInput witness

theorem canonicalPublicInput?_statementOf (spec : ConstraintSystemSpec)
    (system : spec.System) (publicInput : spec.PublicInput) :
    spec.canonicalPublicInput? system (spec.statementOf system publicInput) = some publicInput := by
  exact spec.publicInputOf?_statementOf system publicInput

theorem statement_wellFormed (spec : ConstraintSystemSpec)
    (system : spec.System) (publicInput : spec.PublicInput) :
    spec.WellFormedStatement system (spec.statementOf system publicInput) := by
  exact ⟨publicInput, spec.publicInputOf?_statementOf system publicInput⟩

theorem statementOf_injective (spec : ConstraintSystemSpec)
    (system : spec.System) :
    Function.Injective (spec.statementOf system) := by
  intro publicInput₁ publicInput₂ hstmt
  have h₁ := spec.publicInputOf?_statementOf system publicInput₁
  have h₂ := spec.publicInputOf?_statementOf system publicInput₂
  rw [hstmt] at h₁
  exact Option.some.inj (h₁.symm.trans h₂)

theorem realizesStatement_of_satisfies (spec : ConstraintSystemSpec)
    (system : spec.System) (publicInput : spec.PublicInput) (witness : spec.Witness)
    (hsat : spec.satisfies system publicInput witness) :
    spec.realizesStatement system (spec.statementOf system publicInput) witness := by
  exact ⟨publicInput, spec.publicInputOf?_statementOf system publicInput, hsat⟩

theorem realizesStatement_iff (spec : ConstraintSystemSpec)
    (system : spec.System) (publicInput : spec.PublicInput) (witness : spec.Witness) :
    spec.realizesStatement system (spec.statementOf system publicInput) witness ↔
      spec.satisfies system publicInput witness := by
  constructor
  · intro hrealizes
    rcases hrealizes with ⟨publicInput', hstmt, hsat⟩
    have hcanon := spec.publicInputOf?_statementOf system publicInput
    have hEq : publicInput' = publicInput := by
      exact Option.some.inj (hstmt.symm.trans hcanon)
    simpa [hEq] using hsat
  · intro hsat
    exact spec.realizesStatement_of_satisfies system publicInput witness hsat

end ConstraintSystemSpec

end Zklib.Core
