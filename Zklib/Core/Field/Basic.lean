namespace Zklib.Core

/--
A minimal operational signature for prime-field level structure.

This stays intentionally small until the repository decides how much of the
eventual algebraic hierarchy should come from local interfaces versus mathlib.
-/
structure PrimeFieldOps where
  Carrier : Type
  zero : Carrier
  one : Carrier
  add : Carrier -> Carrier -> Carrier
  mul : Carrier -> Carrier -> Carrier
  neg : Carrier -> Carrier

end Zklib.Core
