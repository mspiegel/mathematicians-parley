module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/binet-formula.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.BinetFormula.PowerRecurrence

theorem power_recurrence (x : ℝ) (hH2 : x ^ 2 = x + 1) (k : ℕ) :
    x ^ (k + 1 + 1) = x ^ (k + 1) + x ^ k := by
  -- 1. mun:exponent-step a := x, m := k
  have s1 : x ^ (k + 1) = x ^ k * x := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := x) (m := k)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := x) (m := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := x) (m := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := x) (m := k)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := x) (m := k))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := x) (m := k)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := x) (m := k)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := x) (m := k)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := x) (m := k)); parley_side)
  -- 2. mun:exponent-step a := x, m := k + 1
  have s2 : x ^ (k + 1 + 1) = x ^ (k + 1) * x := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := x) (m := k + 1)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := x) (m := k + 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := x) (m := k + 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := x) (m := k + 1)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := x) (m := k + 1))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := x) (m := k + 1)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := x) (m := k + 1)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := x) (m := k + 1)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := x) (m := k + 1)); parley_side)
  -- 3. calculation
  have s3 : x ^ (k + 1 + 1) = x ^ (k + 1) + x ^ k := by
    calc x ^ (k + 1 + 1) = x ^ k * x * x := by linear_combination (norm := parley_norm) (x) * s1 + s2
      _ = x ^ k * (x + 1) := by linear_combination (norm := parley_norm) (x ^ k) * hH2
      _ = x ^ (k + 1) + x ^ k := by linear_combination (norm := parley_norm) (-1) * s1
  all_goals parley_side

end Parley.Proofs.Hammack.BinetFormula.PowerRecurrence
