import Zklib.Core.Field

namespace Zklib.Core

/--
An extension-field skeleton layered on top of a base field signature.

Future work should replace this with a more semantic formulation once the field
hierarchy is stable.
-/
structure ExtensionFieldSkeleton where
  base : PrimeFieldOps
  Carrier : Type
  degree : Nat

end Zklib.Core
