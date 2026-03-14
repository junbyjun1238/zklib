import Zklib.Core.ConstraintSystem

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
  blobOfClaim? : Claim -> Option Blob
  blobOfClaim?_claimOf : ∀ blob, blobOfClaim? (claimOf blob) = some blob
  proves : Setup -> Commitment -> Claim -> Proof -> Prop
  verify : Setup -> Blob -> Commitment -> Proof -> Prop
  verify_sound :
    ∀ setup blob commitment proof,
      verify setup blob commitment proof ->
        proves setup commitment (claimOf blob) proof

namespace EIP4844VerifierSpec

/--
The canonical commitment attached to a blob under a given setup.
-/
def canonicalCommitment (spec : EIP4844VerifierSpec)
    (setup : spec.Setup) (blob : spec.Blob) : spec.Commitment :=
  spec.commitmentOf setup blob

/--
The canonical claim attached to a blob.
-/
def canonicalClaim (spec : EIP4844VerifierSpec) (blob : spec.Blob) : spec.Claim :=
  spec.claimOf blob

/--
Verify a proof against the canonical commitment derived from the blob.
-/
def verifiesCanonical (spec : EIP4844VerifierSpec)
    (setup : spec.Setup) (blob : spec.Blob) (proof : spec.Proof) : Prop :=
  spec.verify setup blob (spec.canonicalCommitment setup blob) proof

/--
The statement-system pair used to view EIP-4844 verification inside the generic
constraint-system semantics layer.
-/
def canonicalSystem (spec : EIP4844VerifierSpec)
    (setup : spec.Setup) (commitment : spec.Commitment) : spec.Setup × spec.Commitment :=
  (setup, commitment)

/--
View the EIP-4844 verifier boundary as a generic statement system whose
statements are claims, public inputs are blobs, and witnesses are proofs.
-/
def toConstraintSystemSpec (spec : EIP4844VerifierSpec) : Zklib.Core.ConstraintSystemSpec where
  System := spec.Setup × spec.Commitment
  PublicInput := spec.Blob
  Witness := spec.Proof
  Statement := spec.Claim
  statementOf := fun _ blob => spec.claimOf blob
  publicInputOf? := fun _ claim => spec.blobOfClaim? claim
  publicInputOf?_statementOf := by
    intro _ blob
    exact spec.blobOfClaim?_claimOf blob
  satisfies := fun system blob proof =>
    spec.proves system.1 system.2 (spec.claimOf blob) proof

theorem canonicalClaim_wellFormed (spec : EIP4844VerifierSpec)
    (setup : spec.Setup) (commitment : spec.Commitment) (blob : spec.Blob) :
    (spec.toConstraintSystemSpec).WellFormedStatement
      (spec.canonicalSystem setup commitment) (spec.canonicalClaim blob) := by
  exact
    Zklib.Core.ConstraintSystemSpec.statement_wellFormed
      (spec := spec.toConstraintSystemSpec)
      (system := spec.canonicalSystem setup commitment)
      (publicInput := blob)

theorem proves_realizesCanonicalClaim (spec : EIP4844VerifierSpec)
    (setup : spec.Setup) (commitment : spec.Commitment)
    (blob : spec.Blob) (proof : spec.Proof)
    (hproves : spec.proves setup commitment (spec.canonicalClaim blob) proof) :
    (spec.toConstraintSystemSpec).realizesStatement
      (spec.canonicalSystem setup commitment) (spec.canonicalClaim blob) proof := by
  exact
    Zklib.Core.ConstraintSystemSpec.realizesStatement_of_satisfies
      (spec := spec.toConstraintSystemSpec)
      (system := spec.canonicalSystem setup commitment)
      (publicInput := blob)
      (witness := proof)
      hproves

theorem verifiesCanonical_sound (spec : EIP4844VerifierSpec)
    (setup : spec.Setup) (blob : spec.Blob) (proof : spec.Proof)
    (hverify : spec.verifiesCanonical setup blob proof) :
    spec.proves setup (spec.canonicalCommitment setup blob) (spec.canonicalClaim blob) proof := by
  exact spec.verify_sound setup blob (spec.canonicalCommitment setup blob) proof hverify

theorem verifiesCanonical_realizesCanonicalClaim (spec : EIP4844VerifierSpec)
    (setup : spec.Setup) (blob : spec.Blob) (proof : spec.Proof)
    (hverify : spec.verifiesCanonical setup blob proof) :
    (spec.toConstraintSystemSpec).realizesStatement
      (spec.canonicalSystem setup (spec.canonicalCommitment setup blob))
      (spec.canonicalClaim blob) proof := by
  exact spec.proves_realizesCanonicalClaim setup (spec.canonicalCommitment setup blob)
    blob proof (spec.verifiesCanonical_sound setup blob proof hverify)

end EIP4844VerifierSpec

end Zklib.Instantiations
