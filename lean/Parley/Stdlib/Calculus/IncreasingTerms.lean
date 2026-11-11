module

public import Functions
public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from corpus/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Calculus.IncreasingTerms

theorem increasing_terms (x : ℤ → ℝ) (hH2 : ∀ n : ℤ, 0 < n → x n ≤ x (n + 1)) :
    (∀ n : ℤ, 0 < n → (∀ m : ℤ, 0 < m → m ≤ n → x m ≤ x n)) := by
  -- 1. induction on n starting at 1
  intro n h_n
  replace h_n : 1 ≤ n := by omega
  induction n, h_n using LeanBridges.Functions.le_induction with
  | base =>
    intro m hK1
    intro hA1
    -- 1.1. inequalities, from K1
    have s1_1 : 1 ≤ m := by parley_order
    -- 1.2. antisymmetry, from A1, 1.1
    have s1_2 : m = 1 := by parley_side
    -- 1.3. substitute m = 1 (line 1.2)
    have s1_3 : x m = x 1 := by (have h := congrArg (fun t : ℤ => x t) s1_2; push_cast at h ⊢; all_goals exact_mod_cast h)
    -- 1.4. inequalities
    parley_order
  | succ n hK hIH =>
    intro m hK1
    intro hA1
    -- 1.5. mun:le-cases x := m, y := n + 1, from A1
    have s1_5 : m < n + 1 ∨ m = n + 1 := by exact ((Parley.Items.Stdlib.Numbers.mun_le_cases (x := m) (y := n + 1))).mp hA1
    -- 1.6. cases, from 1.5
    rcases s1_5 with hC1 | hC2
    · skip
      -- 1.6.1. mun:integer-step n := n + 1, from C1
      have s1_6_1 : m + 1 ≤ n + 1 := by exact (Parley.Items.Stdlib.Numbers.mun_integer_step (m := m) (n := n + 1) hC1)
      -- 1.6.2. inequalities
      have s1_6_2 : m ≤ n := by parley_order
      -- 1.6.3. instantiate m := m in IH, from 1.6.2
      have s1_6_3 : x m ≤ x n := by exact (hIH m hK1 s1_6_2)
      -- 1.6.4. instantiate n := n in H2
      have s1_6_4 : x n ≤ x (n + 1) := by exact (hH2 n (lt_of_lt_of_le zero_lt_one hK))
      -- 1.6.5. transitivity, from 1.6.3, 1.6.4
      exact le_trans s1_6_3 s1_6_4
    · skip
      -- 1.6.6. substitute m = n + 1 (C2)
      have s1_6_6 : x m = x (n + 1) := by (have h := congrArg (fun t : ℤ => x t) hC2; push_cast at h ⊢; all_goals exact_mod_cast h)
      -- 1.6.7. inequalities
      parley_order

end Parley.Stdlib.Calculus.IncreasingTerms
