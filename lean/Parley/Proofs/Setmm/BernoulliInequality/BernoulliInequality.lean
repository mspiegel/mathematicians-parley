module

public import AlgebraTactics
public import Functions
public import OrderTactics
public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Setmm.BernoulliInequality.NonnegativeProduct

/-! Written from proofs/setmm/bernoulli-inequality.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.BernoulliInequality.BernoulliInequality

set_option maxHeartbeats 400000 in
theorem bernoulli_inequality (A : ℝ) (hH2 : 0 ≤ A) (n : ℤ) (hH3 : 0 ≤ n) :
    (A - 1) * (n : ℝ) + 1 ≤ A ^ n.toNat := by
  -- 1. induction on k starting at 0
  have s1 : ∀ k : ℤ, 0 ≤ k → (A - 1) * (k : ℝ) + 1 ≤ A ^ k.toNat := by
    intro k h_k
    replace h_k : 0 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. algebra
      have s1_1 : A ^ 0 = 1 := by parley_ring
      -- 1.2. inequalities
      have s1_2 : (A - 1) * 0 + 1 ≤ A ^ 0 := by parley_order
      all_goals parley_side
    | succ k hK hIH =>
      -- 1.3. mun:exponent-step a := A, m := k
      have s1_3 : A ^ (k + 1).toNat = A ^ k.toNat * A := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := A) (m := k) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := A) (m := k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := A) (m := k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := A) (m := k) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := A) (m := k) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := A) (m := k) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := A) (m := k) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := A) (m := k) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := A) (m := k) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := A) (m := k) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := A) (m := k) (by parley_side)); parley_side)
      -- 1.4. inequalities
      have s1_4 : 0 ≤ A ^ k.toNat - ((A - 1) * (k : ℝ) + 1) := by parley_order
      set X : ℝ := A ^ k.toNat - ((A - 1) * (k : ℝ) + 1) with hD1
      have hD1_kind : True := by parley_side
      -- 1.5. thm:nonnegative-product x := A, y := X, from D1, H2, 1.4
      have s1_5 : 0 ≤ A * X := by
        try simp only [hD1] at *
        try push_cast at *
        first | (have h := (Parley.Proofs.Setmm.BernoulliInequality.NonnegativeProduct.nonnegative_product (x := A) (y := A ^ k.toNat - ((A - 1) * (k : ℝ) + 1)) hH2 s1_4); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [(Parley.Proofs.Setmm.BernoulliInequality.NonnegativeProduct.nonnegative_product (x := A) (y := A ^ k.toNat - ((A - 1) * (k : ℝ) + 1)) hH2 s1_4)] | (have h := (Parley.Proofs.Setmm.BernoulliInequality.NonnegativeProduct.nonnegative_product (x := A) (y := A ^ k.toNat - ((A - 1) * (k : ℝ) + 1)) hH2 s1_4); push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Setmm.BernoulliInequality.NonnegativeProduct.nonnegative_product (x := A) (y := A ^ k.toNat - ((A - 1) * (k : ℝ) + 1)) hH2 s1_4) | (have h := (Parley.Proofs.Setmm.BernoulliInequality.NonnegativeProduct.nonnegative_product (x := A) (y := A ^ k.toNat - ((A - 1) * (k : ℝ) + 1)) hH2 s1_4); parley_side)
      -- 1.6. mun:square-nonneg x := A − 1
      have s1_6 : 0 ≤ (A - 1) ^ 2 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := A - 1))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := A - 1)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := A - 1)) | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := A - 1)); parley_side)
      -- 1.7. thm:nonnegative-product x := (A − 1)², y := k, from K, 1.6
      have s1_7 : 0 ≤ (A - 1) ^ 2 * (k : ℝ) := by first | linarith [(Parley.Proofs.Setmm.BernoulliInequality.NonnegativeProduct.nonnegative_product (x := (A - 1) ^ 2) (y := (k : ℝ)) s1_6 (by parley_side))] | (have h := (Parley.Proofs.Setmm.BernoulliInequality.NonnegativeProduct.nonnegative_product (x := (A - 1) ^ 2) (y := (k : ℝ)) s1_6 (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Setmm.BernoulliInequality.NonnegativeProduct.nonnegative_product (x := (A - 1) ^ 2) (y := (k : ℝ)) s1_6 (by parley_side)) | (have h := (Parley.Proofs.Setmm.BernoulliInequality.NonnegativeProduct.nonnegative_product (x := (A - 1) ^ 2) (y := (k : ℝ)) s1_6 (by parley_side)); parley_side)
      -- 1.8. algebra, from D1
      have s1_8 : A ^ k.toNat * A - ((A - 1) * ((k : ℝ) + 1) + 1) = A * X + (A - 1) ^ 2 * (k : ℝ) := by
        try simp only [hD1] at *
        try push_cast at *
        parley_ring
      -- 1.9. inequalities, from 1.5, 1.7
      have s1_9 : 0 ≤ A * X + (A - 1) ^ 2 * (k : ℝ) := by parley_order
      -- 1.10. transitivity, from 1.9, 1.8
      have s1_10 : 0 ≤ A ^ k.toNat * A - ((A - 1) * ((k : ℝ) + 1) + 1) := by parley_order
      -- 1.11. inequalities
      have s1_11 : (A - 1) * ((k : ℝ) + 1) + 1 ≤ A ^ k.toNat * A := by parley_order
      -- 1.12. transitivity, from 1.11, 1.3
      have s1_12 : (A - 1) * ((k : ℝ) + 1) + 1 ≤ A ^ (k + 1).toNat := by parley_order
      all_goals parley_side
  -- 2. instantiate k := n in line 1
  have s2 : (A - 1) * (n : ℝ) + 1 ≤ A ^ n.toNat := by first | (have h := (s1 n (by parley_side)); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [(s1 n (by parley_side))] | (have h := (s1 n (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s1 n (by parley_side)) | (have h := (s1 n (by parley_side)); parley_side)
  all_goals exact s2

end Parley.Proofs.Setmm.BernoulliInequality.BernoulliInequality
