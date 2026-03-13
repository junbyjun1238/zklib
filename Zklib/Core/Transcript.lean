namespace Zklib.Core

/--
A transcript abstraction for Fiat-Shamir style verifier statements.

Messages are typed first and explicitly serialized to bytes before absorption.
That keeps transcript-facing interfaces honest about encoding boundaries instead
of baking in an ad hoc `String` model.
-/
structure TranscriptSpec where
  State : Type
  Challenge : Type
  Message : Type
  encode : Message -> ByteArray
  absorbBytes : State -> ByteArray -> State
  squeeze : State -> Challenge × State

namespace TranscriptSpec

/--
Absorb a typed message after explicit serialization.
-/
def absorb (spec : TranscriptSpec) (state : spec.State) (message : spec.Message) : spec.State :=
  spec.absorbBytes state (spec.encode message)

end TranscriptSpec

end Zklib.Core
