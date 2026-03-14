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
  encodeChallenge : Challenge -> ByteArray
  absorbBytes : State -> ByteArray -> State
  observeChallenge : State -> Challenge -> State
  squeeze : State -> Prod Challenge State
  absorbBytes_empty : ∀ state, absorbBytes state ByteArray.empty = state
  absorbBytes_append :
    ∀ state bytes₁ bytes₂,
      absorbBytes (absorbBytes state bytes₁) bytes₂ = absorbBytes state (bytes₁ ++ bytes₂)
  observeChallenge_eq_absorbBytes :
    ∀ state challenge,
      observeChallenge state challenge = absorbBytes state (encodeChallenge challenge)
  squeeze_updates_state :
    ∀ state,
      (squeeze state).2 = observeChallenge state (squeeze state).1

namespace TranscriptSpec

/--
Absorb a typed message after explicit serialization.
-/
def absorb (spec : TranscriptSpec) (state : TranscriptSpec.State spec)
    (message : TranscriptSpec.Message spec) : TranscriptSpec.State spec :=
  spec.absorbBytes state (spec.encode message)

/--
Record an already-generated challenge in the transcript state.
-/
def absorbChallenge (spec : TranscriptSpec) (state : TranscriptSpec.State spec)
    (challenge : TranscriptSpec.Challenge spec) : TranscriptSpec.State spec :=
  spec.observeChallenge state challenge

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

/--
Repeatedly squeeze challenges, threading the post-squeeze state.
-/
def squeezeMany (spec : TranscriptSpec) (state : TranscriptSpec.State spec)
    (count : Nat) : List (TranscriptSpec.Challenge spec) × TranscriptSpec.State spec :=
  match count with
  | 0 => ([], state)
  | n + 1 =>
      let (challenge, state') := spec.squeeze state
      let (challenges, state'') := spec.squeezeMany state' n
      (challenge :: challenges, state'')

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

theorem absorbChallenge_eq_absorbBytes (spec : TranscriptSpec)
    (state : TranscriptSpec.State spec) (challenge : TranscriptSpec.Challenge spec) :
    spec.absorbChallenge state challenge =
      spec.absorbBytes state (spec.encodeChallenge challenge) := by
  exact spec.observeChallenge_eq_absorbBytes state challenge

theorem squeeze_state_eq_absorbChallenge (spec : TranscriptSpec)
    (state : TranscriptSpec.State spec) :
    (spec.squeeze state).2 = spec.absorbChallenge state (spec.squeeze state).1 := by
  exact spec.squeeze_updates_state state

theorem squeeze_state_eq_absorbChallengeBytes (spec : TranscriptSpec)
    (state : TranscriptSpec.State spec) :
    (spec.squeeze state).2 =
      spec.absorbBytes state (spec.encodeChallenge (spec.squeeze state).1) := by
  rw [spec.squeeze_state_eq_absorbChallenge, spec.absorbChallenge_eq_absorbBytes]

theorem squeezeMany_zero (spec : TranscriptSpec) (state : TranscriptSpec.State spec) :
    spec.squeezeMany state 0 = ([], state) := by
  rfl

theorem squeezeMany_succ (spec : TranscriptSpec) (state : TranscriptSpec.State spec) (n : Nat) :
    spec.squeezeMany state (n + 1) =
      let (challenge, state') := spec.squeeze state
      let (challenges, state'') := spec.squeezeMany state' n
      (challenge :: challenges, state'') := by
  rfl

end TranscriptSpec

end Zklib.Core
