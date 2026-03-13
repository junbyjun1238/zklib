namespace Zklib.Instantiations

/--
zkVM-facing verifier boundary intended for FRI, Merkle, and receipt-style
verification layers.

This stays intentionally light, but it now exposes an explicit statement layer
and verification-key boundary instead of treating receipt verification as an
unstructured boolean boundary.
-/
structure ZkVMVerifierSpec where
  Program : Type
  VerificationKey : Type
  Receipt : Type
  Statement : Type
  verificationKeyOf : Program -> VerificationKey
  statementOf : Program -> Receipt -> Statement
  statementValid : VerificationKey -> Statement -> Prop
  verify : VerificationKey -> Receipt -> Prop

end Zklib.Instantiations
