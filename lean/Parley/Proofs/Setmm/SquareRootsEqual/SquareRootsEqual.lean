module

public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/square-roots-equal.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SquareRootsEqual.SquareRootsEqual

theorem square_roots_equal (a : ℝ) (b : ℝ) (hH3 : 0 ≤ a) (hH4 : 0 ≤ b) :
    (Real.sqrt a = Real.sqrt b ↔ a = b) := by
  -- 1. def:sqrt x := a
  have r12_1 : a ≥ 0 := by parley_side
  have s1 : Real.sqrt a ^ 2 = a := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a) r12_1)
  -- 2. both directions
  constructor
  · skip
    intro hD1
    -- 2.1. substitute √a = √b (D1) into line 1
    have s2_1 : Real.sqrt b ^ 2 = a := by parley_subst_at hD1 s1
    -- 2.2. calculation
    have r25_1 : b ≥ 0 := by parley_side
    calc a = Real.sqrt b ^ 2 := by parley_side
      _ = b := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := b) r25_1)
  · skip
    intro hD2
    -- 2.3. substitute a = b (D2)
    parley_subst hD2

end Parley.Proofs.Setmm.SquareRootsEqual.SquareRootsEqual
