module

public import Functions
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/divisor-of-power.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DivisorOfPower.DivisorOfPower

theorem divisor_of_power (K : ℤ) (M : ℤ) (n : ℤ) (hH3 : 0 < n) (hH4 : K ∣ M) :
    K ∣ M ^ n.toNat := by
  -- 1. induction on m starting at 1
  have s1 : ∀ m : ℤ, 0 < m → K ∣ M ^ m.toNat := by
    intro m h_m
    replace h_m : 1 ≤ m := by omega
    induction m, h_m using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. restate H4
      have s1_1 : K ∣ M ^ 1 := by parley_side
      all_goals parley_side
    | succ m hK hIH =>
      -- 1.2. mun:divides-multiple e := K, a := M^m, x := M, from IH
      have s1_2 : K ∣ M ^ m.toNat * M := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := K) (a := M ^ m.toNat) (x := M) hIH) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := K) (a := M ^ m.toNat) (x := M) hIH)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := K) (a := M ^ m.toNat) (x := M) hIH) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := K) (a := M ^ m.toNat) (x := M) hIH) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := K) (a := M ^ m.toNat) (x := M) hIH); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := K) (a := M ^ m.toNat) (x := M) hIH); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := K) (a := M ^ m.toNat) (x := M) hIH); parley_side)
      -- 1.3. substitute
      have s1_3 : K ∣ M ^ (m + 1).toNat := by
        have c1 : M ^ m.toNat * M = M ^ (m + 1).toNat := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := M) (m := m) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := M) (m := m) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := M) (m := m) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := M) (m := m) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := M) (m := m) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := M) (m := m) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := M) (m := m) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := M) (m := m) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := M) (m := m) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := M) (m := m) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := M) (m := m) (by parley_side)); parley_side)
        have row1 : K ∣ M ^ (m + 1).toNat := by parley_subst_at c1 s1_2
        exact row1
      all_goals parley_side
  -- 2. instantiate m := n in line 1
  have s2 : K ∣ M ^ n.toNat := by first | exact (s1 n (by parley_side)) | exact ((s1 n (by parley_side))).symm | simpa using (s1 n (by parley_side)) | exact_mod_cast (s1 n (by parley_side)) | (have h := (s1 n (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (s1 n (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); parley_side)
  all_goals exact s2

end Parley.Proofs.Setmm.DivisorOfPower.DivisorOfPower
