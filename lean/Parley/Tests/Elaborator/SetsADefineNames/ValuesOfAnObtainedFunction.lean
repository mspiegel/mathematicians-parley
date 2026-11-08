module

public import ArithTactics
public import OrderTactics
public import SetTactics
public import Tactics
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/sets-a-define-names.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.SetsADefineNames.ValuesOfAnObtainedFunction

theorem values_of_an_obtained_function (n : ℤ) (hH1 : 0 < n) (m : ℤ) (hH2 : 0 < m) (hH3 : ∃ f : ℤ → ℤ, Set.MapsTo f (Set.Icc (1 : ℤ) n : Set ℤ) (Set.Icc (1 : ℤ) m : Set ℤ) ∧ f 1 = 1) :
    (∃ f : ℤ → ℤ, Set.MapsTo f (Set.Icc (1 : ℤ) n : Set ℤ) (Set.Icc (1 : ℤ) m : Set ℤ) ∧ f 1 ≤ f 1) := by
  -- 1. obtain g from H3
  obtain ⟨g, s1a, s1b⟩ := hH3
  -- 2. def:range-between k := 1, a := 1, b := n, from H1
  have r115_1 : (1 : ℤ) ≤ 1 := by parley_arith
  have s2 : (1 : ℤ) ∈ Finset.Icc (1 : ℤ) n := ((Parley.Items.Stdlib.Sums.def_range_between (k := (1 : ℤ)) (a := (1 : ℤ)) (b := n))).mpr (by parley_set_side)
  -- 3. inequalities
  have s3 : g 1 ≤ g 1 := by parley_order
  -- 4. exhibit, from 1, 3
  exact ⟨g, by parley_set_side, by parley_set_side⟩

end Parley.Tests.Elaborator.SetsADefineNames.ValuesOfAnObtainedFunction
