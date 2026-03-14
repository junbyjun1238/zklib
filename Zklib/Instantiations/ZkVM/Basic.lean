import Zklib.Core.ConstraintSystem

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
  receiptOfStatement? : Program -> Statement -> Option Receipt
  receiptOfStatement?_statementOf :
    ∀ program receipt,
      receiptOfStatement? program (statementOf program receipt) = some receipt
  statementValid : VerificationKey -> Statement -> Prop
  verify : VerificationKey -> Receipt -> Prop
  verify_sound :
    ∀ program receipt,
      verify (verificationKeyOf program) receipt ->
        statementValid (verificationKeyOf program) (statementOf program receipt)

namespace ZkVMVerifierSpec

/--
The canonical verification key attached to a program.
-/
def canonicalVerificationKey (spec : ZkVMVerifierSpec)
    (program : spec.Program) : spec.VerificationKey :=
  spec.verificationKeyOf program

/--
The canonical statement attached to a `(program, receipt)` pair.
-/
def canonicalStatement (spec : ZkVMVerifierSpec)
    (program : spec.Program) (receipt : spec.Receipt) : spec.Statement :=
  spec.statementOf program receipt

/--
Verify a receipt against the canonical verification key derived from the
program.
-/
def verifiesReceipt (spec : ZkVMVerifierSpec)
    (program : spec.Program) (receipt : spec.Receipt) : Prop :=
  spec.verify (spec.canonicalVerificationKey program) receipt

/--
View the zkVM verifier boundary as a generic statement system whose public
inputs are receipts and whose witness type is trivial.
-/
def toConstraintSystemSpec (spec : ZkVMVerifierSpec) : Zklib.Core.ConstraintSystemSpec where
  System := spec.Program
  PublicInput := spec.Receipt
  Witness := PUnit
  Statement := spec.Statement
  statementOf := spec.statementOf
  publicInputOf? := spec.receiptOfStatement?
  publicInputOf?_statementOf := spec.receiptOfStatement?_statementOf
  satisfies := fun program receipt _ => spec.verifiesReceipt program receipt

theorem canonicalStatement_wellFormed (spec : ZkVMVerifierSpec)
    (program : spec.Program) (receipt : spec.Receipt) :
    (spec.toConstraintSystemSpec).WellFormedStatement
      program (spec.canonicalStatement program receipt) := by
  exact
    Zklib.Core.ConstraintSystemSpec.statement_wellFormed
      (spec := spec.toConstraintSystemSpec)
      (system := program)
      (publicInput := receipt)

theorem verifiesReceipt_sound (spec : ZkVMVerifierSpec)
    (program : spec.Program) (receipt : spec.Receipt)
    (hverify : spec.verifiesReceipt program receipt) :
    spec.statementValid (spec.canonicalVerificationKey program)
      (spec.canonicalStatement program receipt) := by
  exact spec.verify_sound program receipt hverify

theorem verifiesReceipt_realizesCanonicalStatement (spec : ZkVMVerifierSpec)
    (program : spec.Program) (receipt : spec.Receipt)
    (hverify : spec.verifiesReceipt program receipt) :
    (spec.toConstraintSystemSpec).realizesStatement
      program (spec.canonicalStatement program receipt) PUnit.unit := by
  exact
    Zklib.Core.ConstraintSystemSpec.realizesStatement_of_satisfies
      (spec := spec.toConstraintSystemSpec)
      (system := program)
      (publicInput := receipt)
      (witness := PUnit.unit)
      hverify

end ZkVMVerifierSpec

end Zklib.Instantiations
