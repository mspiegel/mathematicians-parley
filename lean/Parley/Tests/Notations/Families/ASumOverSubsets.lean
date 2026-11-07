module

public import NormTactics
public import PowerTactics
public import SetTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sums

/-! Written from tests/notations/families.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Families.ASumOverSubsets

theorem a_sum_over_subsets {α : Type*} (D : Set α) (K : Set (Set α)) (hH2 : K ⊆ 𝒫 D) (hH3 : K.Finite) :
    (∑ᶠ s ∈ K, (1 : ℤ)) = (K.ncard : ℤ) * 1 := by
  -- 1. mun:sum-constant-over X := K, c := 1, from H3
  have s1 : (∑ᶠ s ∈ K, (1 : ℤ)) = (K.ncard : ℤ) * 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_constant_over (X := K) hH3 (c := (1 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_constant_over (X := K) hH3 (c := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_constant_over (X := K) hH3 (c := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | (parley_count_ext; exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_constant_over (X := K) hH3 (c := (1 : ℤ)))) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_constant_over (X := K) hH3 (c := (1 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_constant_over (X := K) hH3 (c := (1 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_constant_over (X := K) hH3 (c := (1 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_constant_over (X := K) hH3 (c := (1 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_constant_over (X := K) hH3 (c := (1 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_constant_over (X := K) hH3 (c := (1 : ℤ))); parley_set_side)
  all_goals exact s1

end Parley.Tests.Notations.Families.ASumOverSubsets
