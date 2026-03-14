import Zklib.Core.EvaluationDomain

/-!
Backward-compatibility shim for the earlier `Subgroup` module path.

The repository now uses `EvaluationDomain` as the primary surface because the
current abstraction is a generator-indexed evaluation domain, not general
subgroup theory.
-/
