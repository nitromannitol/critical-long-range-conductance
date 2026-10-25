import Lake

open Lake DSL

package «longRange» where

require «lattice-probability» from git
  "https://github.com/nitromannitol/Lattice-Probability.git" @
    "47027b49b6660ee34c323869b0c88b7eb72f1124"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "81a5d257c8e410db227a6665ed08f64fea08e997"

@[default_target]
lean_lib «LongRange» where
  globs := #[.andSubmodules `LongRange]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]
