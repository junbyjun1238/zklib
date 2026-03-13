namespace Zklib.Instantiations

/--
Ethereum-facing verifier boundary for EIP-4844 style KZG verification.
-/
structure EIP4844VerifierSpec where
  Blob : Type
  Commitment : Type
  Proof : Type
  verify : Blob -> Commitment -> Proof -> Prop

end Zklib.Instantiations
