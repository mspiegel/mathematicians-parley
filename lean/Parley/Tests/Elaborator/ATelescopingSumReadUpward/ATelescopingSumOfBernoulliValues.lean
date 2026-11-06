module

public import OrderTactics
public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/a-telescoping-sum-read-upward.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ATelescopingSumReadUpward.ATelescopingSumOfBernoulliValues

theorem a_telescoping_sum_of_bernoulli_values (m : ℤ) (hH1 : 0 ≤ m) :
    (∑ n ∈ Finset.Icc (0 : ℤ) m, (Polynomial.aeval ((n : ℂ) + 1) (Polynomial.bernoulli 2) - Polynomial.aeval (n : ℂ) (Polynomial.bernoulli 2) : ℂ)) = Polynomial.aeval ((m : ℂ) + 1) (Polynomial.bernoulli 2) - Polynomial.aeval (0 : ℂ) (Polynomial.bernoulli 2) := by
  -- 1. thm:sum-telescopes-up a := 0, b := m
  have r18_1 : m + 1 ≥ 0 := by parley_order
  have s1 : (∑ n ∈ Finset.Icc (0 : ℤ) m, (Polynomial.aeval ((n : ℂ) + 1) (Polynomial.bernoulli 2) - Polynomial.aeval (n : ℂ) (Polynomial.bernoulli 2) : ℂ)) = Polynomial.aeval ((m : ℂ) + 1) (Polynomial.bernoulli 2) - Polynomial.aeval (0 : ℂ) (Polynomial.bernoulli 2) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.thm_sum_telescopes_up (t := (fun n : ℤ => Polynomial.aeval (n : ℂ) (Polynomial.bernoulli 2))) (a := (0 : ℤ)) (b := m) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.thm_sum_telescopes_up (t := (fun n : ℤ => Polynomial.aeval (n : ℂ) (Polynomial.bernoulli 2))) (a := (0 : ℤ)) (b := m) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.thm_sum_telescopes_up (t := (fun n : ℤ => Polynomial.aeval (n : ℂ) (Polynomial.bernoulli 2))) (a := (0 : ℤ)) (b := m) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.thm_sum_telescopes_up (t := (fun n : ℤ => Polynomial.aeval (n : ℂ) (Polynomial.bernoulli 2))) (a := (0 : ℤ)) (b := m) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.thm_sum_telescopes_up (t := (fun n : ℤ => Polynomial.aeval (n : ℂ) (Polynomial.bernoulli 2))) (a := (0 : ℤ)) (b := m) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.thm_sum_telescopes_up (t := (fun n : ℤ => Polynomial.aeval (n : ℂ) (Polynomial.bernoulli 2))) (a := (0 : ℤ)) (b := m) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.thm_sum_telescopes_up (t := (fun n : ℤ => Polynomial.aeval (n : ℂ) (Polynomial.bernoulli 2))) (a := (0 : ℤ)) (b := m) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.thm_sum_telescopes_up (t := (fun n : ℤ => Polynomial.aeval (n : ℂ) (Polynomial.bernoulli 2))) (a := (0 : ℤ)) (b := m) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.thm_sum_telescopes_up (t := (fun n : ℤ => Polynomial.aeval (n : ℂ) (Polynomial.bernoulli 2))) (a := (0 : ℤ)) (b := m) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ATelescopingSumReadUpward.ATelescopingSumOfBernoulliValues
