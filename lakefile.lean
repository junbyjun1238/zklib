import Lake
open Lake DSL

/- 
Dependency revisions are pinned through `lake-manifest.json`.
Run `lake update` only when intentionally refreshing those pins.
-/
package zklib where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib Zklib where
