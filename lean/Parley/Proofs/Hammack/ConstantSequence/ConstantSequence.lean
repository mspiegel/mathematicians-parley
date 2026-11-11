module

public import NormTactics
public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/constant-sequence.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ConstantSequence.ConstantSequence

theorem constant_sequence (c : ℝ) (a : ℤ → ℝ) (hH3 : ∀ n : ℤ, 0 < n → a n = c) :
    Filter.Tendsto (fun n : ℤ => (a n : ℝ)) Filter.atTop (nhds c) := by
  -- 1. proof
  have s1 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (a n - c) < ε)) := by
    intro ε
    intro hA1
    -- 1.1. proof
    have s1_1 : ∀ n : ℤ, 0 < n → n ≥ 1 → abs (a n - c) < ε := by
      intro n hK2
      intro hA2
      -- 1.1.1. algebra, from H3
      have s1_1_1 : a n - c = 0 := by linear_combination (norm := parley_norm) (hH3 n (by parley_side))
      -- 1.1.2. calculation
      have s1_1_2 : abs (a n - c) = 0 := by
        calc abs (a n - c) = abs 0 := by (have h := congrArg (fun t : ℝ => abs t) s1_1_1; push_cast at h ⊢; all_goals exact_mod_cast h)
          _ = 0 := by exact_mod_cast Parley.Items.Stdlib.Numbers.mun_abs_zero
      -- 1.1.3. transitivity, from 1.1.2, A1
      parley_order
    -- 1.2. exhibit, from 1.1
    exact ⟨(1 : ℤ), by parley_side, s1_1⟩
  -- 2. def:tends-to L := c, from 1
  exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := c))).mpr s1

end Parley.Proofs.Hammack.ConstantSequence.ConstantSequence
