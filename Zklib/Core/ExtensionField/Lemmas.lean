import Zklib.Core.ExtensionField.Basic

universe u v

namespace Zklib.Core

section

variable {K : Type u} {L : Type v}
variable [Field K] [Field L] [Algebra K L]

theorem extensionDegree_eq_finrank :
    extensionDegree K L = Module.finrank K L := by
  rfl

end

end Zklib.Core
