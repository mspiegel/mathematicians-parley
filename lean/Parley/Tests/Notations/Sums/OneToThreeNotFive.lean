module

public import LeanBridges
public import Parley.Tests.Notations.Sums.OneToThreeSummed

/-! Written from tests/notations/sums.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Sums.OneToThreeNotFive

theorem one_to_three_not_five :
    (∑ k ∈ Finset.Icc (1 : ℤ) (3 : ℤ), (k : ℤ)) ≠ 5 := by
  -- 1. thm:one-to-three-summed
  have s1 : (∑ k ∈ Finset.Icc (1 : ℤ) (3 : ℤ), (k : ℤ)) = 6 := by first | linear_combination (norm := parley_norm) Parley.Tests.Notations.Sums.OneToThreeSummed.one_to_three_summed | (have h := Parley.Tests.Notations.Sums.OneToThreeSummed.one_to_three_summed; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Tests.Notations.Sums.OneToThreeSummed.one_to_three_summed; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast Parley.Tests.Notations.Sums.OneToThreeSummed.one_to_three_summed | exact_mod_cast (Parley.Tests.Notations.Sums.OneToThreeSummed.one_to_three_summed).symm | (have h := Parley.Tests.Notations.Sums.OneToThreeSummed.one_to_three_summed; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Tests.Notations.Sums.OneToThreeSummed.one_to_three_summed; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Tests.Notations.Sums.OneToThreeSummed.one_to_three_summed; parley_int_power h) | (have h := Parley.Tests.Notations.Sums.OneToThreeSummed.one_to_three_summed; parley_side)
  -- 2. contradiction
  have s2 : (∑ k ∈ Finset.Icc (1 : ℤ) (3 : ℤ), (k : ℤ)) ≠ 5 := by
    by_contra hc_hS
    have hS : (∑ k ∈ Finset.Icc (1 : ℤ) (3 : ℤ), (k : ℤ)) = 5 := by parley_suppose hc_hS
    -- 2.1. calculation
    have s2_1 : (6 : ℤ) = 5 := by
      calc (6 : ℤ) = (∑ k ∈ Finset.Icc (1 : ℤ) (3 : ℤ), (k : ℤ)) := by parley_side
        _ = 5 := by parley_side
    exact absurd s2_1 (by norm_num)
    all_goals parley_side
  all_goals parley_side

end Parley.Tests.Notations.Sums.OneToThreeNotFive
