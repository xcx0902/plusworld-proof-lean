import Lake
open Lake DSL

package "plusworld-proof" where
  version := v!"0.1.0"
  packagesDir := "../lib/packages"

require mathlib from "../lib/mathlib4"

@[default_target]
lean_lib «PlusworldProof» where
