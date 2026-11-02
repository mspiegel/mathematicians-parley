module

public import LeanBridges
public import Parley.Items.Stdlib.Reasoning

/-! Written from tests/stdlib/reasoning.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Reasoning.DoubleNegation

theorem double_negation (x : ℝ) (hH2 : ¬ x ≠ 0) :
    x = 0 := by
  -- 1. mun:reasoning-double-negation P := x = 0, from H2
  have s1 : x = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := x = 0) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := x = 0) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := x = 0) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Reasoning.mun_double_negation (P := x = 0) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := x = 0) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := x = 0) (by parley_side)); qify; linear_combination (norm := parley_norm) h)
  all_goals parley_side

end Parley.Tests.Stdlib.Reasoning.DoubleNegation
