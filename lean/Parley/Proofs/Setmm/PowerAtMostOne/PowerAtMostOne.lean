module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/power-at-most-one.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.PowerAtMostOne.PowerAtMostOne

theorem power_at_most_one (a : ℝ) (n : ℕ) (hH3 : 0 ≤ a) (hH4 : a ≤ 1) :
    a ^ n ≤ 1 := by
  -- 1. induction on m starting at 0
  have s1 : ∀ m : ℕ, a ^ m ≤ 1 := by
    intro m
    induction m with
    | zero =>
      -- 1.1. algebra
      have s1_1 : a ^ 0 = 1 := by parley_ring
      -- 1.2. inequalities
      have s1_2 : a ^ 0 ≤ 1 := by parley_order
      all_goals parley_side
    | succ m hIH =>
      -- 1.3. mun:exponent-step
      have s1_3 : a ^ (m + 1) = a ^ m * a := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := m)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := m)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := m)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := m)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := m))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := m)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := m)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := m)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := m)); parley_side)
      -- 1.4. algebra
      have s1_4 : a ^ m * a = a * a ^ m := by parley_ring
      -- 1.5. axi:trichotomy x := a
      have s1_5 : (a < 0 ∨ a = 0) ∨ 0 < a := by first | exact (Parley.Items.Stdlib.Numbers.axi_trichotomy (x := a)) | exact ((Parley.Items.Stdlib.Numbers.axi_trichotomy (x := a))).symm | simpa using (Parley.Items.Stdlib.Numbers.axi_trichotomy (x := a)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.axi_trichotomy (x := a)) | (have h := (Parley.Items.Stdlib.Numbers.axi_trichotomy (x := a)); parley_side)
      -- 1.6. cases, from 1.5
      have s1_6 : a ^ (m + 1) ≤ 1 := by
        rcases s1_5 with (hC1 | hC2) | hC3
        · skip
          -- 1.6.1. inequalities, from C1
          have s1_6_1 : ¬ 0 ≤ a := by parley_side
          all_goals parley_side
        · skip
          -- 1.6.2. algebra, from C2
          have s1_6_2 : a * a ^ m = 0 := by linear_combination (norm := parley_norm) (a ^ m) * hC2
          -- 1.6.3. arithmetic
          have s1_6_3 : (0 : ℤ) ≤ 1 := by parley_arith
          -- 1.6.4. transitivity, from 1.3, 1.4, 1.6.2, 1.6.3
          have s1_6_4 : a ^ (m + 1) ≤ 1 := by parley_order
          all_goals parley_side
        · skip
          -- 1.6.5. mun:multiply-le x := a^m, y := 1, c := a, from C3, IH
          have s1_6_5 : a * a ^ m ≤ a * 1 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_multiply_le (x := a ^ m) (y := (1 : ℝ)) (c := a) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := a ^ m) (y := (1 : ℝ)) (c := a) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := a ^ m) (y := (1 : ℝ)) (c := a) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := a ^ m) (y := (1 : ℝ)) (c := a) (by parley_side) (by parley_side)); parley_side)
          -- 1.6.6. inequalities
          have s1_6_6 : a * a ^ m ≤ a := by parley_order
          -- 1.6.7. transitivity, from 1.3, 1.4, 1.6.6, H4
          have s1_6_7 : a ^ (m + 1) ≤ 1 := by parley_order
          all_goals parley_side
      all_goals parley_side
  -- 2. instantiate m := n in line 1
  have s2 : a ^ n ≤ 1 := by first | linarith [(s1 n)] | (have h := (s1 n); push_cast at h; linarith) | exact_mod_cast (s1 n) | (have h := (s1 n); parley_side)
  all_goals parley_side

end Parley.Proofs.Setmm.PowerAtMostOne.PowerAtMostOne
