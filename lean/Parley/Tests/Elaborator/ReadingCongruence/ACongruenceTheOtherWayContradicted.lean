module

public import ArithTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.ModEq

/-! Written from tests/elaborator/reading-congruence.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingCongruence.ACongruenceTheOtherWayContradicted

theorem a_congruence_the_other_way_contradicted (a : ℤ) (b : ℤ) (n : ℤ) (hH3 : 0 < n) (hH4 : b ≡ a [ZMOD n]) :
    a ≡ b [ZMOD n] := by
  -- 1. contradiction
  have s1 : a ≡ b [ZMOD n] := by
    by_contra hc_hS
    have hS : ¬ a ≡ b [ZMOD n] := by parley_suppose hc_hS
    -- 1.1. restate S
    have s1_1 : ¬ a ≡ b [ZMOD n] := by parley_side
    all_goals parley_side
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingCongruence.ACongruenceTheOtherWayContradicted
