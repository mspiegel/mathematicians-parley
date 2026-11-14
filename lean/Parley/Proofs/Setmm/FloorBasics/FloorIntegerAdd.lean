module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Floor
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Setmm.FloorBasics.FloorAddInteger

/-! Written from proofs/setmm/floor-basics.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.FloorBasics.FloorIntegerAdd

theorem floor_integer_add (N : ℤ) (A : ℝ) :
    ⌊(N : ℝ) + A⌋ = N + ⌊A⌋ := by
  -- 1. mun:floor-integer x := A
  -- 2. algebra
  have s2 : (N : ℝ) + A = A + (N : ℝ) := by ring1
  -- 3. calculation
  calc ⌊(N : ℝ) + A⌋ = ⌊A + (N : ℝ)⌋ := by (have h := congrArg (fun t : ℝ => (⌊t⌋ : ℝ)) s2; push_cast at h ⊢; exact_mod_cast h)
    _ = ⌊A⌋ + N := by exact (Parley.Proofs.Setmm.FloorBasics.FloorAddInteger.floor_add_integer (A := A) (N := N))
    _ = N + ⌊A⌋ := by ring1

end Parley.Proofs.Setmm.FloorBasics.FloorIntegerAdd
