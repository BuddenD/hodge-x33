import Lake
open Lake DSL

package HodgeX33 where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"

@[default_target]
lean_lib HodgeX33 where
  globs := #[.one `HodgeX33]
