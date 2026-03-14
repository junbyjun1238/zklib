import Zklib.Core.NTT.Radix2.Basic
import Zklib.Core.NTT.Radix2.Correctness
import Zklib.Core.NTT.Radix2.CosetBasic
import Zklib.Core.NTT.Radix2.CosetCorrectness
import Zklib.Core.NTT.Radix2.CoefficientSplit
import Zklib.Core.NTT.Radix2.CosetCoefficientSplit

/-!
`Zklib.Core.NTT.Radix2.Semantics` contains radix-2 domain structure and
structural transform lemmas that do not yet commit to a concrete list, array,
or tree implementation.

In particular, this layer records even/odd decomposition and butterfly-shaped
identities for the semantic transform itself.
-/
