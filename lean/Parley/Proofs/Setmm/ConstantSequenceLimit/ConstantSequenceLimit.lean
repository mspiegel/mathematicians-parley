module

public import NormTactics
public import OrderTactics
public import PowerTactics
public import SubstTactics
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
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Topology.Defs.Filter
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/constant-sequence-limit.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ConstantSequenceLimit.ConstantSequenceLimit

theorem constant_sequence_limit (c : ℝ) (x : ℤ → ℝ) (hH3 : ∀ n : ℤ, 0 < n → x n = c) :
    Filter.Tendsto (fun n : ℤ => (x n : ℝ)) Filter.atTop (nhds c) := by
  -- 1. proof
  have s1 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (x n - c) < ε)) := by
    intro ε
    intro hA1
    -- 1.1. proof
    have s1_1 : ∀ n : ℤ, 0 < n → n ≥ 1 → abs (x n - c) < ε := by
      intro n hK2
      intro hA2
      -- 1.1.1. algebra, from H3
      have s1_1_1 : x n - c = 0 := by linear_combination (norm := parley_norm) (hH3 n (by parley_side))
      -- 1.1.2. calculation
      have s1_1_2 : abs (x n - c) = 0 := by
        calc abs (x n - c) = abs 0 := by parley_subst s1_1_1
          _ = 0 := by first | linear_combination (norm := parley_norm) Parley.Items.Stdlib.Numbers.mun_abs_zero | (have h := Parley.Items.Stdlib.Numbers.mun_abs_zero; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Numbers.mun_abs_zero; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast Parley.Items.Stdlib.Numbers.mun_abs_zero | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_abs_zero).symm | (have h := Parley.Items.Stdlib.Numbers.mun_abs_zero; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Numbers.mun_abs_zero; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Numbers.mun_abs_zero; parley_int_power h) | (have h := Parley.Items.Stdlib.Numbers.mun_abs_zero; parley_side)
      -- 1.1.3. transitivity, from 1.1.2, A1
      have s1_1_3 : abs (x n - c) < ε := by parley_order
      all_goals parley_side
    -- 1.2. exhibit, from 1.1
    have s1_2 : ∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (x n - c) < ε) := ⟨(1 : ℤ), by parley_side, by parley_side⟩
    all_goals parley_side
  -- 2. def:tends-to L := c, from 1
  have s2 : Filter.Tendsto (fun n : ℤ => (x n : ℝ)) Filter.atTop (nhds c) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := c))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := c))).mpr (by parley_side); parley_side)
  all_goals exact s2

end Parley.Proofs.Setmm.ConstantSequenceLimit.ConstantSequenceLimit
