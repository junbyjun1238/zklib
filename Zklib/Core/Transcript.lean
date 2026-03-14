universe u v w

namespace Zklib.Core

/--
A transcript abstraction for Fiat-Shamir style verifier statements.

Messages are typed first and explicitly serialized to bytes before absorption.
That keeps transcript-facing interfaces honest about encoding boundaries instead
of baking in an ad hoc `String` model. The minimal laws below make sequencing
explicit enough for verifier-level proofs to talk about transcript state
composition, not just individual absorb/squeeze calls.
-/
structure TranscriptSpec where
  State : Type u
  Challenge : Type v
  Message : Type w
  encode : Message -> ByteArray
  absorbBytes : State -> ByteArray -> State
  squeeze : State -> Prod Challenge State
  absorbBytes_empty : ∀ state, absorbBytes state ByteArray.empty = state
  absorbBytes_append :
    ∀ state bytes₁ bytes₂,
      absorbBytes (absorbBytes state bytes₁) bytes₂ = absorbBytes state (bytes₁ ++ bytes₂)

namespace TranscriptSpec

/--
Absorb a typed message after explicit serialization.
-/
def absorb (spec : TranscriptSpec) (state : TranscriptSpec.State spec)
    (message : TranscriptSpec.Message spec) : TranscriptSpec.State spec :=
  spec.absorbBytes state (spec.encode message)

/--
Absorb a sequence of already-serialized byte chunks.
-/
def absorbManyBytes (spec : TranscriptSpec) (state : TranscriptSpec.State spec)
    (chunks : List ByteArray) : TranscriptSpec.State spec :=
  chunks.foldl spec.absorbBytes state

/--
Absorb a sequence of typed messages.
-/
def absorbMany (spec : TranscriptSpec) (state : TranscriptSpec.State spec)
    (messages : List (TranscriptSpec.Message spec)) : TranscriptSpec.State spec :=
  spec.absorbManyBytes state (messages.map spec.encode)

theorem absorbManyBytes_nil (spec : TranscriptSpec) (state : TranscriptSpec.State spec) :
    spec.absorbManyBytes state [] = state := by
  rfl

theorem absorbManyBytes_cons (spec : TranscriptSpec) (state : TranscriptSpec.State spec)
    (chunk : ByteArray) (chunks : List ByteArray) :
    spec.absorbManyBytes state (chunk :: chunks) =
      spec.absorbManyBytes (spec.absorbBytes state chunk) chunks := by
  rfl

theorem absorbBytes_two_eq_absorbManyBytes (spec : TranscriptSpec)
    (state : TranscriptSpec.State spec) (bytes₁ bytes₂ : ByteArray) :
    spec.absorbManyBytes state [bytes₁, bytes₂] = spec.absorbBytes state (bytes₁ ++ bytes₂) := by
  simp [absorbManyBytes, spec.absorbBytes_append]

theorem absorb_eq_absorbMany_singleton (spec : TranscriptSpec)
    (state : TranscriptSpec.State spec) (message : TranscriptSpec.Message spec) :
    spec.absorb state message = spec.absorbMany state [message] := by
  rfl

end TranscriptSpec

end Zklib.Core
