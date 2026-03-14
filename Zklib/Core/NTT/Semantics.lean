import Zklib.Core.NTT.Basic
import Zklib.Core.NTT.Correctness

/-!
`Zklib.Core.NTT.Semantics` exposes the meaning of an NTT as evaluation on a
chosen domain together with canonical interpolation back from value tables.

These imports are intentionally semantic: they describe what the transform is
and the interpolation-level laws it satisfies, without committing to any FFT
implementation strategy.
-/
