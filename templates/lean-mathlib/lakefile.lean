import Lake
open Lake DSL

-- This defines your Lean package/project
-- Change "myproject" to your actual project name
package myproject where
  -- Lean compiler options
  leanOptions := #[
    -- Disables automatic implicit arguments
    -- This means you must explicitly declare all type parameters
    -- Recommended for mathematical proofs to avoid confusion
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

-- Dependencies: This pulls in Mathlib, Lean's mathematical library
-- Mathlib provides thousands of pre-proven theorems and mathematical structures
-- like groups, rings, topology, analysis, etc.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

-- This defines a Lean library (collection of Lean files)
-- @[default_target] means this is what gets built when you run `lake build`
@[default_target]
lean_lib «Main» where
  -- roots tells Lake which Lean files are entry points
  -- `Main` means it looks for Main.lean in the project root
  -- For multiple files, use: roots := #[`File1, `File2, `Subdir.File3]
  roots := #[`Main]
