import Lake
open Lake DSL

package SchematicMath where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "9d44f295b1de1c2a2c91bcb7dae8d5b0b15839c4"

@[default_target]
lean_lib SchematicMath where
  roots := #[`Schematic.Math]
