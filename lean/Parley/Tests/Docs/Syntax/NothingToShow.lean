module

public import SetTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.TypeStar

/-! Written from tests/docs/syntax.proof by parley build lean. -/

public section

namespace Parley.Tests.Docs.Syntax.NothingToShow

theorem nothing_to_show {α : Type*} (V : Set α) (n : ℤ) (hH1 : 0 ≤ n) (v : ℤ → α) (hH3 : Set.MapsTo v {n : ℤ | 0 ≤ n} V) :
    (∀ x ∈ V, (0 ≤ n ∧ x = v (0 : ℤ)) ∧ ¬ x = v (0 : ℤ) → x = v n) := by
  -- 1. proof
  have s1 : ∀ x ∈ V, (0 ≤ n ∧ x = v (0 : ℤ)) ∧ ¬ x = v (0 : ℤ) → x = v n := by
    intro x hK1
    -- 1.1. proof
    have s1_1 : (0 ≤ n ∧ x = v (0 : ℤ)) ∧ ¬ x = v (0 : ℤ) → x = v n := by
      intro hC2
      -- 1.1.1. restate C2
      have s1_1_1 : x = v (0 : ℤ) := by parley_set_side
      -- 1.1.2. restate C2
      have s1_1_2 : ¬ x = v (0 : ℤ) := by parley_set_side
      all_goals parley_set_side
    all_goals exact s1_1
  all_goals exact s1

end Parley.Tests.Docs.Syntax.NothingToShow
