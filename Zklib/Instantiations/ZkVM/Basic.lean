namespace Zklib.Instantiations

/--
zkVM-facing verifier boundary intended for FRI, Merkle, and receipt-style
verification layers.

This stays intentionally light, but it now exposes an explicit statement layer
instead of treating receipt verification as an unstructured boolean boundary.
-/
structure ZkVMVerifierSpec where
  Program : Type
  Receipt : Type
  Statement : Type
  statementOf : Program -> Receipt -> Statement
  verify : Program -> Receipt -> Prop

end Zklib.Instantiations
