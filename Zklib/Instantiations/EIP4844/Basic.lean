namespace Zklib.Instantiations

/--
Ethereum-facing verifier boundary for EIP-4844 style KZG verification.

This is still a boundary-level interface, but it now makes the verification
shape explicit: a blob determines a setup-indexed commitment-side claim, and
proofs are checked against that claim under a setup.
-/
structure EIP4844VerifierSpec where
  Setup : Type
  Blob : Type
  Commitment : Type
  Claim : Type
  Proof : Type
  commitmentOf : Setup -> Blob -> Commitment
  claimOf : Blob -> Claim
  proves : Setup -> Commitment -> Claim -> Proof -> Prop
  verify : Setup -> Blob -> Commitment -> Proof -> Prop

end Zklib.Instantiations
