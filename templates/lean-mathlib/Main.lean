-- Import mathematical structures from Mathlib
-- This gives you access to real numbers, basic arithmetic, etc.
import Mathlib.Data.Real.Basic

-- A simple example showing Lean can be used for:
-- 1. Mathematical proofs (like the theorem below)
-- 2. Executable programs (like the main function)

/-- This is a theorem stating that 2 + 2 = 4
    The /-- syntax creates documentation -/
theorem two_plus_two : 2 + 2 = 4 := by
  -- 'by' starts a proof
  -- 'norm_num' is a tactic that simplifies numerical expressions
  norm_num

/-- A function that doubles a natural number -/
def double (n : Nat) : Nat := 2 * n

-- This makes the file executable
-- When you run the program, this function gets called
def main : IO Unit := do
  -- IO.println prints to the console
  -- s! is string interpolation
  IO.println s!"Hello from Lean with Mathlib!"
  IO.println s!"2 + 2 = {2 + 2}"
  IO.println s!"double 21 = {double 21}"

  -- You can also use Mathlib's mathematical structures
  let x : ℝ := 3.14  -- ℝ is the real numbers type from Mathlib
  IO.println s!"A real number: {x}"
