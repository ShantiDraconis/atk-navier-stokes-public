import Lake
open Lake DSL

package «m-private» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "fe17e590176eea00b6912e09ed52280cc0d60128"

@[default_target]
lean_lib MPrivate where
