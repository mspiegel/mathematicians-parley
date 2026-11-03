module

public import Tactics
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/a-sum-over-a-compound-of-a-defined-function.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ASumOverACompoundOfADefinedFunction.ASumOfSquaresOfARecursion

theorem a_sum_of_squares_of_a_recursion (F : ℤ → ℤ) (hD1 : F 0 = (1 : ℤ) ∧ ∀ k : ℤ, 0 ≤ k → F (k + 1) = F k + 1) (hH1 : True) :
    (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (F j ^ 2 : ℤ)) = F 1 ^ 2 := by
  -- 1. mun:sum-single a := 1, from H1
  have s1 : (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (F j ^ 2 : ℤ)) = F 1 ^ 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => F j ^ 2)) (a := (1 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => F j ^ 2)) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => F j ^ 2)) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => F j ^ 2)) (a := (1 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => F j ^ 2)) (a := (1 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => F j ^ 2)) (a := (1 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => F j ^ 2)) (a := (1 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => F j ^ 2)) (a := (1 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => F j ^ 2)) (a := (1 : ℤ))); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ASumOverACompoundOfADefinedFunction.ASumOfSquaresOfARecursion
