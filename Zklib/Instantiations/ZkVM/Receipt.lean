import Zklib.Instantiations.ZkVM.Basic

namespace Zklib.Instantiations

/--
Placeholder theorem boundary for zkVM receipt verification developments.
-/
theorem ZkVMVerifierSpec.placeholder
    (spec : ZkVMVerifierSpec) :
    ∀ program receipt,
      spec.verify (spec.verificationKeyOf program) receipt ->
        spec.statementValid (spec.verificationKeyOf program) (spec.statementOf program receipt) := by
  sorry

end Zklib.Instantiations
