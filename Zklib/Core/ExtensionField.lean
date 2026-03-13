import Zklib.Core.Field

namespace Zklib.Core

/--
An extension-field placeholder layered on top of a base field specification.

Future work should replace this with a more semantic formulation once the field
hierarchy is stable.
-/
structure ExtensionFieldSpec where
  base : PrimeFieldSpec
  Carrier : Type
  degree : Nat

end Zklib.Core
