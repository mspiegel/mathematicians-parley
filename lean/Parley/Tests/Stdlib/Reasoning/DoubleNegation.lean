module

public import Tactics
public import Parley.Items.Stdlib.Reasoning

/-! Written from tests/stdlib/reasoning.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Reasoning.DoubleNegation

theorem double_negation (x : ℝ) (hH2 : ¬ x ≠ 0) :
    x = 0 := by
  -- 1. mun:reasoning-double-negation P := x = 0, from H2
  have s1 : x = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := x = 0) hH2) | (have h := (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := x = 0) hH2); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := x = 0) hH2); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := x = 0) hH2) | exact_mod_cast ((Parley.Items.Stdlib.Reasoning.mun_double_negation (P := x = 0) hH2)).symm | (have h := (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := x = 0) hH2); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := x = 0) hH2); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := x = 0) hH2); parley_int_power h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := x = 0) hH2); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Reasoning.DoubleNegation
