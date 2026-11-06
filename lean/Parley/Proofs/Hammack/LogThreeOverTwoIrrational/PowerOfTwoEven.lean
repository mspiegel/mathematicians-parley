module

public import AlgebraTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/log-three-over-two-irrational.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.LogThreeOverTwoIrrational.PowerOfTwoEven

theorem power_of_two_even (n : ℤ) (hH1 : 0 < n) :
    Even (2 ^ n.toNat : ℤ) := by
  -- 1. mun:nat-minus-one
  have s1 : 0 ≤ n - 1 := by first | exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := n) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := n) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := n) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := n) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := n) (by parley_side)); parley_side)
  -- 2. mun:exponent-step a := 2, m := n − 1, from 1
  have s2 : (2 ^ (n - 1 + 1) : ℚ) = 2 ^ (n - 1) * 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℚ)) (m := n - 1) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℚ)) (m := n - 1) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℚ)) (m := n - 1) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℚ)) (m := n - 1) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℚ)) (m := n - 1) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℚ)) (m := n - 1) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℚ)) (m := n - 1) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℚ)) (m := n - 1) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℚ)) (m := n - 1) (by parley_side)); parley_side)
  -- 3. substitute
  have s3 : (2 ^ n.toNat : ℚ) = 2 ^ (n - 1) * 2 := by
    have c1 : n - 1 + 1 = n := by parley_ring
    have c1_w : (n : ℚ) - 1 + 1 = (n : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) c1; push_cast at h; linear_combination (norm := parley_norm) h
    have row1 : (2 ^ n.toNat : ℚ) = 2 ^ (n - 1) * 2 := by first | parley_put_at c1_w s2 | parley_put_at c1 s2 | parley_subst_at c1_w s2 | parley_subst_at c1 s2
    exact row1
  -- 4. algebra, from 3
  have s4 : (2 ^ n.toNat : ℚ) = 2 * 2 ^ (n - 1) := by linear_combination (norm := parley_norm) s3
  -- 5. mun:power-integer a := 2, m := n − 1, from 1
  have s5 : ∃ m : ℤ, (m : ℚ) = 2 ^ (n - 1) := by
    have whole1 : ((2 : ℚ) : ℚ) ^ (n - 1).toNat = (2 ^ (n - 1) : ℚ) := by rw [← zpow_natCast, Int.toNat_of_nonneg s1]
    exact ⟨(((2 : ℤ) ^ (n - 1).toNat) : ℤ), by first | (push_cast; simp only [whole1]; done) | (push_cast; simp only [whole1]; ring)⟩
  -- 6. def:even n := 2^n, from 4, 5
  have s6 : Even (2 ^ n.toNat : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := (2 ^ n.toNat : ℤ)))).mpr ⟨Classical.choose s5, by have := Classical.choose_spec s5; parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := (2 ^ n.toNat : ℤ)))).mpr ⟨Classical.choose s5, by have := Classical.choose_spec s5; parley_side⟩; parley_side)
  all_goals exact s6

end Parley.Proofs.Hammack.LogThreeOverTwoIrrational.PowerOfTwoEven
