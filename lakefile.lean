import Lake
open Lake DSL

package «uu» where
  version := v!"0.1.0"

require VCVio from git
  "https://github.com/Verified-zkEVM/VCV-io.git" @
  "93493459bfa72112af025e1b1cfc6caa79ad8aa9"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "v4.29.0"

@[default_target]
lean_lib Uu

lean_exe uu where
  root := `Main
