module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/power-at-least-one.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.PowerAtLeastOne.PowerAtLeastOne

theorem power_at_least_one (a : ℝ) (n : ℕ) (hH3 : 1 ≤ a) :
    1 ≤ a ^ n := by
  -- 1. inequalities, from H3
  have s1 : a > 0 := by parley_order
  -- 2. induction on m starting at 0
  have s2 : ∀ m : ℕ, 1 ≤ a ^ m := by
    intro m
    induction m with
    | zero =>
      -- 2.1. algebra
      have s2_1 : a ^ 0 = 1 := by parley_ring
      -- 2.2. inequalities
      have s2_2 : 1 ≤ a ^ 0 := by parley_order
      all_goals parley_side
    | succ m hIH =>
      -- 2.3. mun:exponent-step
      have s2_3 : a ^ (m + 1) = a ^ m * a := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := m)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := m)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := m)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := m)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := m))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := m)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := m)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := m)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := m)); parley_side)
      -- 2.4. mun:multiply-le x := 1, y := a^m, c := a, from IH, 1
      have s2_4 : a * 1 ≤ a * a ^ m := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℝ)) (y := a ^ m) (c := a) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℝ)) (y := a ^ m) (c := a) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℝ)) (y := a ^ m) (c := a) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℝ)) (y := a ^ m) (c := a) (by parley_side) (by parley_side)); parley_side)
      -- 2.5. inequalities
      have s2_5 : a ≤ a ^ m * a := by parley_order
      -- 2.6. transitivity, from H3, 2.5, 2.3
      have s2_6 : 1 ≤ a ^ (m + 1) := by parley_order
      all_goals parley_side
  -- 3. instantiate m := n in line 2
  have s3 : 1 ≤ a ^ n := by first | linarith [(s2 n)] | (have h := (s2 n); push_cast at h; linarith) | exact_mod_cast (s2 n) | (have h := (s2 n); parley_side)
  all_goals exact s3

end Parley.Proofs.Setmm.PowerAtLeastOne.PowerAtLeastOne
