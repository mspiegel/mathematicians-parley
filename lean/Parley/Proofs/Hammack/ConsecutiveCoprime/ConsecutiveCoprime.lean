module

public import LeanBridges
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/hammack/consecutive-coprime.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ConsecutiveCoprime.ConsecutiveCoprime

theorem consecutive_coprime (n : ℕ) :
    (Int.gcd (n : ℤ) ((n : ℤ) + 1) : ℤ) = 1 := by
  -- 1. axi:excluded-middle P := n = 0
  have s1 : (n : ℤ) = 0 ∨ (n : ℤ) ≠ 0 := by first | exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := (n : ℤ) = 0)) | exact ((Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := (n : ℤ) = 0))).symm | simpa using (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := (n : ℤ) = 0)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := (n : ℤ) = 0)) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := (n : ℤ) = 0)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := (n : ℤ) = 0)); parley_side)
  -- 2. cases, from 1
  have s2 : (Int.gcd (n : ℤ) ((n : ℤ) + 1) : ℤ) = 1 := by
    rcases s1 with hC1 | hC2
    · skip
      -- 2.1. calculation
      have s2_1 : (Int.gcd (n : ℤ) ((n : ℤ) + 1) : ℤ) = 1 := by
        calc (Int.gcd (n : ℤ) ((n : ℤ) + 1) : ℤ) = (Int.gcd (0 : ℤ) (1 : ℤ) : ℤ) := by parley_subst hC1
          _ = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_gcd_one (a := (0 : ℤ))) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_one (a := (0 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_one (a := (0 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_gcd_one (a := (0 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_gcd_one (a := (0 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_one (a := (0 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_one (a := (0 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_one (a := (0 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_one (a := (0 : ℤ))); parley_side)
      all_goals parley_side
    · skip
      -- 2.2. mun:nat0-nonzero m := n, from C2
      have s2_2 : 0 < n := by first | exact (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := n) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := n) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := n) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := n) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := n) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := n) (by parley_side)); parley_side)
      -- 2.3. def:gcd a := n, b := n + 1, from 2.2
      have s2_3a : 0 < (Int.gcd (n : ℤ) ((n : ℤ) + 1) : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := n) (by parley_side) (b := n + 1) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := n) (by parley_side) (b := n + 1) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := n) (by parley_side) (b := n + 1) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := n) (by parley_side) (b := n + 1) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := n) (by parley_side) (b := n + 1) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := n) (by parley_side) (b := n + 1) (by parley_side)); parley_side)
      have s2_3b : (Int.gcd (n : ℤ) ((n : ℤ) + 1) : ℤ) ∣ (n : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := n) (by parley_side) (b := n + 1) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := n) (by parley_side) (b := n + 1) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := n) (by parley_side) (b := n + 1) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := n) (by parley_side) (b := n + 1) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := n) (by parley_side) (b := n + 1) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := n) (by parley_side) (b := n + 1) (by parley_side)); parley_side)
      have s2_3c : (Int.gcd (n : ℤ) ((n : ℤ) + 1) : ℤ) ∣ (n : ℤ) + 1 := by first | exact (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := n) (by parley_side) (b := n + 1) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := n) (by parley_side) (b := n + 1) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := n) (by parley_side) (b := n + 1) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := n) (by parley_side) (b := n + 1) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := n) (by parley_side) (b := n + 1) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := n) (by parley_side) (b := n + 1) (by parley_side)); parley_side)
      -- 2.4. mun:divides-difference d := gcd(n, n + 1), a := n + 1, b := n, from 2.3
      have s2_4 : (Int.gcd (n : ℤ) ((n : ℤ) + 1) : ℤ) ∣ (n : ℤ) + 1 - (n : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (Int.gcd (n : ℤ) ((n : ℤ) + 1) : ℤ)) (a := (n : ℤ) + 1) (b := (n : ℤ)) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (Int.gcd (n : ℤ) ((n : ℤ) + 1) : ℤ)) (a := (n : ℤ) + 1) (b := (n : ℤ)) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (Int.gcd (n : ℤ) ((n : ℤ) + 1) : ℤ)) (a := (n : ℤ) + 1) (b := (n : ℤ)) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (Int.gcd (n : ℤ) ((n : ℤ) + 1) : ℤ)) (a := (n : ℤ) + 1) (b := (n : ℤ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (Int.gcd (n : ℤ) ((n : ℤ) + 1) : ℤ)) (a := (n : ℤ) + 1) (b := (n : ℤ)) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (Int.gcd (n : ℤ) ((n : ℤ) + 1) : ℤ)) (a := (n : ℤ) + 1) (b := (n : ℤ)) (by parley_side) (by parley_side)); parley_side)
      -- 2.5. substitute
      have s2_5 : (Int.gcd (n : ℤ) ((n : ℤ) + 1) : ℤ) ∣ (1 : ℤ) := by
        have c1 : (n : ℤ) + 1 - (n : ℤ) = 1 := by parley_ring
        have row1 : (Int.gcd (n : ℤ) ((n : ℤ) + 1) : ℤ) ∣ (1 : ℤ) := by parley_subst_at c1 s2_4
        exact row1
      -- 2.6. mun:divides-one d := gcd(n, n + 1), from 2.3, 2.5
      have s2_6 : (Int.gcd (n : ℤ) ((n : ℤ) + 1) : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := Int.gcd (n : ℤ) ((n : ℤ) + 1)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := Int.gcd (n : ℤ) ((n : ℤ) + 1)) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := Int.gcd (n : ℤ) ((n : ℤ) + 1)) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := Int.gcd (n : ℤ) ((n : ℤ) + 1)) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_divides_one (d := Int.gcd (n : ℤ) ((n : ℤ) + 1)) (by parley_side) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := Int.gcd (n : ℤ) ((n : ℤ) + 1)) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := Int.gcd (n : ℤ) ((n : ℤ) + 1)) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := Int.gcd (n : ℤ) ((n : ℤ) + 1)) (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := Int.gcd (n : ℤ) ((n : ℤ) + 1)) (by parley_side) (by parley_side)); parley_side)
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.ConsecutiveCoprime.ConsecutiveCoprime
