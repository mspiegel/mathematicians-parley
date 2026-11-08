module

public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Topology.Defs.Filter
public import Parley.Items.Stdlib.Calculus
public import Parley.Stdlib.Numbers.AbsBounds

/-! Written from corpus/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Calculus.ConvergentBounded

theorem convergent_bounded (x : ℤ → ℝ) (L : ℝ) (hH3 : Filter.Tendsto (fun n : ℤ => (x n : ℝ)) Filter.atTop (nhds L)) :
    (∃ B : ℝ, ∀ m : ℤ, 0 < m → x m ≤ B) := by
  -- 1. obtain B: thm:convergent-abs-bounded, from H3
  obtain ⟨B, s1⟩ := (Parley.Items.Stdlib.Calculus.thm_convergent_abs_bounded (x := x) (L := L) hH3)
  -- 2. proof
  have s2 : ∀ m : ℤ, 0 < m → x m ≤ B := by
    intro m hK1
    -- 2.1. instantiate i := m in line 1
    have s2_1 : abs (x m) ≤ B := by first | linarith [(s1 m (by parley_side))] | (have h := (s1 m (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s1 m (by parley_side)) | (have h := (s1 m (by parley_side)); parley_side)
    -- 2.2. mun:abs-bounds x := x(m)
    have s2_2 : x m ≤ abs (x m) := by exact (Parley.Stdlib.Numbers.AbsBounds.abs_bounds (x := x m)).1
    -- 2.3. transitivity, from 2.2, 2.1
    parley_order
  -- 3. exhibit, from 2
  exact ⟨B, s2⟩

end Parley.Stdlib.Calculus.ConvergentBounded
