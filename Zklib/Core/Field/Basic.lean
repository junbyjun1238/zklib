import Mathlib.Algebra.Field.Basic

universe u

namespace Zklib.Core

/--
`zklib` does not maintain a custom algebra hierarchy for rings or fields.

Core developments should use `mathlib` typeclasses such as `[CommRing R]` and
`[Field F]` directly.
-/
def UsesMathlibFieldClasses : Prop := True

end Zklib.Core
