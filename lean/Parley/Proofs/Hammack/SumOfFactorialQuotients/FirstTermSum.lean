module

public import Parley.Items.Stdlib.Sums
public import Parley.Library

/-! Written from proofs/hammack/sum-of-factorial-quotients.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SumOfFactorialQuotients.FirstTermSum

theorem first_term_sum (t : ℤ → ℝ) :
    (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), t j) = t 1 := by
  -- 1. mun:sum-single a := 1
  have s1 : (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), t j) = t 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_single (t := t) (a := (1 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := t) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_single (t := t) (a := (1 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_single (t := t) (a := (1 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := t) (a := (1 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := t) (a := (1 : ℤ))); qify; linear_combination (norm := parley_norm) h)
  all_goals parley_side

end Parley.Proofs.Hammack.SumOfFactorialQuotients.FirstTermSum
