module

public import Tactics
public import Parley.Items.Stdlib.Logarithms

/-! Written from tests/stdlib/logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Logarithms.ExpPositive

theorem exp_positive (x : ℝ) :
    Real.exp x > 0 := by
  -- 1. mun:logarithms-exp-positive
  have s1 : Real.exp x > 0 := by first | linarith [(Parley.Items.Stdlib.Logarithms.mun_exp_positive (x := x))] | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_positive (x := x)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Logarithms.mun_exp_positive (x := x)) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_positive (x := x)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Logarithms.ExpPositive
