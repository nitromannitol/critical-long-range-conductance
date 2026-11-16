import Lake

open Lake DSL

package «longRange» where

require «lattice-probability» from git
  "https://github.com/nitromannitol/Lattice-Probability.git" @
    "721505023bc12a20241c73449ec33339fcf4555f"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "065356127b1dc0016f66b7283ce0ce2c4055aa55"

@[default_target]
lean_lib «LongRange» where
  globs := #[.andSubmodules `LongRange]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

/-- The heat-kernel version: quantitative homogenization of the heat equation and the annealed
invariance principle. -/
lean_lib «LongRangeHeat» where
  globs := #[.andSubmodules `LongRangeHeat]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]
