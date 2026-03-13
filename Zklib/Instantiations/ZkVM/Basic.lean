namespace Zklib.Instantiations

/--
zkVM-facing verifier boundary intended for FRI, Merkle, and receipt-style
verification layers.
-/
structure ZkVMVerifierSpec where
  Program : Type
  Receipt : Type
  verify : Program -> Receipt -> Prop

end Zklib.Instantiations
