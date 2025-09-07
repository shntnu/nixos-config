# Lean Project Template (Work in Progress)

> [!WARNING]
> This will become a proper Nix flake template. Currently it's just example files you can copy manually.
> TODO: Add flake.nix to make this work with `nix flake new -t github:shntnu/nixos-config#lean-mathlib`

## What is Lean?
Lean is a functional programming language and interactive theorem prover. You can use it to:
- Write mathematical proofs that are verified by the computer
- Build regular programs (it compiles to efficient C code)
- Explore mathematics interactively with immediate feedback

## Prerequisites

You need Lean installed via Nix (either through your nixos-config or as a Nix package). This ensures a consistent, reproducible development environment.

## To use this template:

```bash
# Copy the template (if you have this repo cloned)
cp -r ~/Documents/GitHub/nix/nixos-config-shntnu/templates/lean-mathlib ~/my-lean-project
cd ~/my-lean-project

# Build your project (Elan will auto-download the right Lean version if needed)
lake build

# Run the executable
lake exe myproject
```

## What's included:
- **`lean-toolchain`** - Specifies which version of Lean to use (stable)
- **`lakefile.lean`** - Build configuration with extensive comments
- **`Main.lean`** - Example starter file with comments explaining Lean basics

## Key Concepts for New Users:

### Lake (Lean's Build System)
- `lake build` - Compiles your Lean files and checks all proofs
- `lake exe <name>` - Runs an executable target
- `lake update` - Updates dependencies (like Mathlib)
- `lake clean` - Removes build artifacts

### File Structure
```
my-project/
├── Main.lean           # Your main Lean file
├── MyModule.lean       # Additional modules (optional)
├── MyModule/
│   └── SubModule.lean  # Nested modules (optional)
├── lakefile.lean       # Build configuration
└── lean-toolchain      # Lean version
```

### Basic Lean Syntax
- **Definitions**: `def myFunction (x : Nat) : Nat := x + 1`
- **Theorems**: `theorem myProof : 2 + 2 = 4 := by norm_num`
- **Types**: `Nat` (natural numbers), `Int` (integers), `ℝ` (reals from Mathlib)
- **Proofs**: Start with `by` and use tactics like `simp`, `norm_num`, `ring`, etc.

## To customize for your project:

1. **Change the package name** in `lakefile.lean`:
   ```lean
   package myproject where  →  package yourname where
   ```

2. **Add new Lean files**: Create `.lean` files and add them to roots in `lakefile.lean`:
   ```lean
   roots := #[`Main, `YourModule, `Another.Module]
   ```

3. **Add more Mathlib imports** in your `.lean` files:
   ```lean
   import Mathlib.Data.Real.Basic      -- Real numbers
   import Mathlib.Analysis.Calculus    -- Calculus
   import Mathlib.Topology.Basic       -- Topology
   import Mathlib.Algebra.Group.Defs   -- Group theory
   ```

## Learning Resources:
- [Lean 4 Documentation](https://leanprover.github.io/documentation/)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/) - Learn to prove theorems
- [Functional Programming in Lean](https://leanprover.github.io/functional_programming_in_lean/) - Learn to program
- [Mathlib4 Docs](https://leanprover-community.github.io/mathlib4_docs/) - Browse available mathematics

## VS Code Setup:
Install the "Lean 4" extension for the best experience:
- Inline error messages
- Proof state visualization
- Auto-completion
- Go-to-definition
