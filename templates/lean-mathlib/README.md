# Lean 4 Project Template with Mathlib

This is a Nix flake template for Lean 4 development with Mathlib support. It provides a complete, reproducible development environment using Nix and elan (Lean's version manager).

## What is Lean?
Lean is a functional programming language and interactive theorem prover. You can use it to:
- Write mathematical proofs that are verified by the computer
- Build regular programs (it compiles to efficient C code)
- Explore mathematics interactively with immediate feedback

## Quick Start

### Create a new project from this template:

```bash
# Create a new Lean project using this template
nix flake new -t github:shntnu/nixos-config#lean-mathlib my-lean-project
cd my-lean-project

# Enter the development environment
nix develop

# Build your project (Elan will auto-download the right Lean version)
lake build

# Run the executable
lake exe myproject
```

### Or use directly without installing globally:

```bash
# Clone and enter the development shell
git clone <your-project>
cd <your-project>
nix develop

# Now you have access to Lean, Lake, and all development tools
lake build
```

## What's included:
- **`lean-toolchain`** - Specifies which version of Lean to use (matches Mathlib's requirement)
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

2. **Change the executable name** in `lakefile.lean`:
   ```lean
   lean_exe «myproject» where  →  lean_exe «yourapp» where
   ```
   Then run with `lake exe yourapp`

3. **Add new Lean files**: Create `.lean` files and add them to roots in `lakefile.lean`:
   ```lean
   roots := #[`Main, `YourModule, `Another.Module]
   ```

4. **Add more Mathlib imports** in your `.lean` files:
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
