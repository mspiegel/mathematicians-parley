module

public import AlgebraTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Setmm.FloorBasics.FloorAddInteger

/-! Written from proofs/setmm/floor-basics.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.FloorBasics.FloorIntegerAdd

theorem floor_integer_add (N : ℤ) (A : ℝ) :
    ⌊(N : ℝ) + A⌋ = N + ⌊A⌋ := by
  -- 1. mun:floor-integer x := A
  -- 2. algebra
  have s2 : (N : ℝ) + A = A + (N : ℝ) := by parley_ring
  -- 3. calculation
  have s3 : ⌊(N : ℝ) + A⌋ = N + ⌊A⌋ := by
    calc ⌊(N : ℝ) + A⌋ = ⌊A + (N : ℝ)⌋ := by parley_subst s2
      _ = ⌊A⌋ + N := by exact (Parley.Proofs.Setmm.FloorBasics.FloorAddInteger.floor_add_integer (A := A) (N := N))
      _ = N + ⌊A⌋ := by parley_ring
  all_goals exact s3

end Parley.Proofs.Setmm.FloorBasics.FloorIntegerAdd
