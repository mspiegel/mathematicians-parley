module

public import NormTactics
public import PowerTactics
public import SetTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Sums

/-! Written from tests/stdlib/sums.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Sums.SumEmptySet

theorem sum_empty_set :
    (∑ᶠ k ∈ (∅ : Set ℤ), (k ^ 2 : ℤ)) = 0 := by
  -- 1. mun:sums-sum-empty-set
  have s1 : (∑ᶠ k ∈ (∅ : Set ℤ), (k ^ 2 : ℤ)) = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_empty_set (t := (fun k : ℤ => k ^ 2))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_empty_set (t := (fun k : ℤ => k ^ 2))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_empty_set (t := (fun k : ℤ => k ^ 2))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_empty_set (t := (fun k : ℤ => k ^ 2))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_empty_set (t := (fun k : ℤ => k ^ 2)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_empty_set (t := (fun k : ℤ => k ^ 2))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_empty_set (t := (fun k : ℤ => k ^ 2))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_empty_set (t := (fun k : ℤ => k ^ 2))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_empty_set (t := (fun k : ℤ => k ^ 2))); parley_set_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Sums.SumEmptySet
