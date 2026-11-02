module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/power-above-one.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.PowerAboveOne.PowerAboveOne

theorem power_above_one (A : ℝ) (hH2 : 1 < A) (n : ℕ) (hH3 : 0 < n) :
    1 < A ^ n := by
  -- 1. induction on k starting at 1
  have s1 : ∀ k : ℕ, 0 < k → 1 < A ^ k := by
    intro k h_k
    replace h_k : 1 ≤ k := h_k
    induction k, h_k using Nat.le_induction with
    | base =>
      -- 1.1. restate H2
      have s1_1 : 1 < A ^ 1 := by parley_side
      all_goals parley_side
    | succ k hK hIH =>
      -- 1.2. inequalities
      have s1_2 : 1 ≤ A ^ k := by parley_side
      -- 1.3. inequalities, from H2
      have s1_3 : 0 < A := by parley_side
      -- 1.4. mun:multiply-le x := 1, y := A^k, c := A, from 1.2, 1.3
      have s1_4 : A * 1 ≤ A * A ^ k := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℝ)) (y := A ^ k) (c := A) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℝ)) (y := A ^ k) (c := A) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℝ)) (y := A ^ k) (c := A) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℝ)) (y := A ^ k) (c := A) (by parley_side) (by parley_side)); parley_side)
      -- 1.5. inequalities
      have s1_5 : A ≤ A * A ^ k := by parley_side
      -- 1.6. transitivity, from H2, 1.5
      have s1_6 : 1 < A * A ^ k := by parley_side
      -- 1.7. calculation
      have s1_7 : 1 < A ^ (k + 1) := by
        calc (1 : ℝ) < A * A ^ k := by parley_side
          _ = A ^ k * A := by parley_ring
          _ = A ^ (k + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := A) (m := k)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := A) (m := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := A) (m := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := A) (m := k)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := A) (m := k))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := A) (m := k)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := A) (m := k)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := A) (m := k)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := A) (m := k)); parley_side)
      all_goals parley_side
  -- 2. instantiate k := n in line 1
  have s2 : 1 < A ^ n := by first | linarith [(s1 n (by parley_side))] | (have h := (s1 n (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s1 n (by parley_side)) | (have h := (s1 n (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Proofs.Setmm.PowerAboveOne.PowerAboveOne
