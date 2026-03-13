namespace Zklib.Core

/--
A transcript abstraction for Fiat-Shamir style verifier statements.
-/
structure TranscriptSpec where
  State : Type
  Challenge : Type
  absorb : State -> String -> State
  squeeze : State -> Challenge × State

end Zklib.Core
