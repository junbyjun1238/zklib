import Mathlib.Algebra.Algebra.Basic
import Mathlib.LinearAlgebra.Dimension.Finite

universe u v

namespace Zklib.Core

/--
`zklib` models extension fields directly through `mathlib` typeclasses such as
`[Field K]`, `[Field L]`, and `[Algebra K L]`.
-/
def UsesMathlibExtensionClasses : Prop := True

/--
The extension degree wrapper exposed directly from `mathlib`'s `finrank`.
-/
noncomputable def extensionDegree (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] : Nat :=
  Module.finrank K L

end Zklib.Core
