namespace Zklib.Core

/--
A deliberately small interface for constraint-system semantics.

This layer is meant to host reusable meaning-level statements that multiple
frontends can target.
-/
structure ConstraintSystemSpec where
  Witness : Type
  Statement : Type
  satisfies : Statement -> Witness -> Prop

end Zklib.Core
