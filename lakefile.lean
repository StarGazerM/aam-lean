import Lake
open Lake DSL

package «aam-lean» where
  -- add package configuration options here

lean_lib «AamLean» where
  -- add library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

require aesop from git "https://github.com/JLimperg/aesop"

@[default_target]
lean_exe «aam-lean» where
  root := `Main
