import Zklib.Showcase.BN254OptimalAte.Basic

namespace Zklib.Showcase

/--
Placeholder theorem boundary for the eventual bilinearity statement.
-/
theorem PairingBilinearityBoundary.placeholder
    (boundary : PairingBilinearityBoundary) : boundary.bilinear := by
  sorry

theorem BN254OptimalAteGoal.placeholder (goal : BN254OptimalAteGoal) : goal.bilinear := by
  exact PairingBilinearityBoundary.placeholder goal

end Zklib.Showcase
