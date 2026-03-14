namespace Zklib.Showcase

/--
Abstract pairing bilinearity boundary for the eventual BN254 optimal Ate
formalization.

This is intentionally more honest than a full BN254 or optimal-Ate
formalization: at the moment it records the algebraic boundary that later
curve-specific developments should discharge.
-/
structure PairingBilinearityBoundary where
  G1 : Type
  G2 : Type
  GT : Type
  addG1 : G1 -> G1 -> G1
  addG2 : G2 -> G2 -> G2
  mulGT : GT -> GT -> GT
  pairing : G1 -> G2 -> GT

namespace PairingBilinearityBoundary

/--
Left-linearity of the abstract pairing boundary.
-/
def leftBilinear (boundary : PairingBilinearityBoundary) : Prop :=
  ∀ p₁ p₂ q,
    boundary.pairing (boundary.addG1 p₁ p₂) q =
      boundary.mulGT (boundary.pairing p₁ q) (boundary.pairing p₂ q)

/--
Right-linearity of the abstract pairing boundary.
-/
def rightBilinear (boundary : PairingBilinearityBoundary) : Prop :=
  ∀ p q₁ q₂,
    boundary.pairing p (boundary.addG2 q₁ q₂) =
      boundary.mulGT (boundary.pairing p q₁) (boundary.pairing p q₂)

/--
The combined bilinearity statement tracked by the showcase goal.
-/
def bilinear (boundary : PairingBilinearityBoundary) : Prop :=
  boundary.leftBilinear ∧ boundary.rightBilinear

theorem bilinear_iff (boundary : PairingBilinearityBoundary) :
    boundary.bilinear ↔ boundary.leftBilinear ∧ boundary.rightBilinear := by
  rfl

end PairingBilinearityBoundary

/--
Backward-compatible alias for the old showcase name.
-/
abbrev BN254OptimalAteBoundary := PairingBilinearityBoundary

/--
Backward-compatible alias kept while the showcase surface is renamed to a more
honest boundary-oriented name.
-/
abbrev BN254OptimalAteGoal := PairingBilinearityBoundary

namespace BN254OptimalAteGoal

theorem bilinear_iff (goal : BN254OptimalAteGoal) :
    goal.bilinear ↔ goal.leftBilinear ∧ goal.rightBilinear := by
  exact PairingBilinearityBoundary.bilinear_iff goal

end BN254OptimalAteGoal

end Zklib.Showcase
