module

public import Tactics
public import Parley.Items.Stdlib.Logarithms

/-! Written from tests/stdlib/logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Logarithms.ExpSum

theorem exp_sum (a : ℂ) (b : ℂ) :
    Complex.exp (a + b) = Complex.exp a * Complex.exp b := by
  -- 1. mun:logarithms-exp-sum
  have s1 : Complex.exp (a + b) = Complex.exp a * Complex.exp b := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Logarithms.mun_exp_sum (a := a) (b := b)) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_sum (a := a) (b := b)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_sum (a := a) (b := b)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Logarithms.mun_exp_sum (a := a) (b := b)) | exact_mod_cast ((Parley.Items.Stdlib.Logarithms.mun_exp_sum (a := a) (b := b))).symm | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_sum (a := a) (b := b)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_sum (a := a) (b := b)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_sum (a := a) (b := b)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_sum (a := a) (b := b)); parley_side)
  all_goals parley_side

end Parley.Tests.Stdlib.Logarithms.ExpSum
