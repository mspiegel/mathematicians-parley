module

public import ArithTactics
public import OrderTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/wiedijk/sqrt2-irrational.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Sqrt2Irrational.LowestTerms

theorem lowest_terms (x : ℚ) :
    (∃ p : ℤ, ∃ q : ℤ, (q > 0 ∧ x = (p : ℚ) / (q : ℚ)) ∧ ¬ (∃ d : ℤ, (d > 1 ∧ d ∣ p) ∧ d ∣ q)) := by
  -- 1. obtain p, q: mun:rational-coprime
  obtain ⟨p, q, s1a, ⟨s1b, s1c⟩⟩ := (Parley.Items.Stdlib.Numbers.mun_rational_coprime (x := x))
  -- 2. contradiction
  have s2 : ¬ (∃ d : ℤ, (d > 1 ∧ d ∣ p) ∧ d ∣ (q : ℤ)) := by
    by_contra hc_hS
    have hS : ∃ d : ℤ, (d > 1 ∧ d ∣ p) ∧ d ∣ (q : ℤ) := by parley_suppose hc_hS
    -- 2.1. obtain d from S
    obtain ⟨d, ⟨⟨s2_1a, s2_1b⟩, s2_1c⟩⟩ := hS
    -- 2.2. thm:divides-gcd a := p, b := q, from 2.1
    have s2_2 : d ∣ (Int.gcd p (q : ℤ) : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := d) (a := p) (b := (q : ℤ)) s2_1b s2_1c) | exact ((Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := d) (a := p) (b := (q : ℤ)) s2_1b s2_1c)).symm | simpa using (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := d) (a := p) (b := (q : ℤ)) s2_1b s2_1c) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := d) (a := p) (b := (q : ℤ)) s2_1b s2_1c) | (have h := (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := d) (a := p) (b := (q : ℤ)) s2_1b s2_1c); parley_side)
    -- 2.3. substitute gcd(p, q) = 1 (line 1) into line 2.2
    have s2_3 : d ∣ (1 : ℤ) := by parley_subst_at s1c s2_2
    -- 2.4. mun:divides-one, from 2.3
    have r83_1 : 0 < d := by parley_order
    have r83_2 : 0 < d := by first | exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := d) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := d) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := d) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := d) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := d) (by parley_side)); parley_side)
    have s2_4 : d = 1 := by first | linear_combination (norm := parley_norm) (Int.toNat_of_nonneg (show (0 : ℤ) ≤ d by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := d.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ d by parley_side)]); parley_side) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ d by parley_side)]); parley_side))) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ d by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := d.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ d by parley_side)]); parley_side) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ d by parley_side)]); parley_side))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ d by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := d.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ d by parley_side)]); parley_side) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ d by parley_side)]); parley_side))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ d by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := d.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ d by parley_side)]); parley_side) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ d by parley_side)]); parley_side))); exact_mod_cast h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ d by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := d.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ d by parley_side)]); parley_side) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ d by parley_side)]); parley_side))); exact_mod_cast h.symm) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ d by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := d.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ d by parley_side)]); parley_side) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ d by parley_side)]); parley_side))); simp (disch := parley_side) only [parley_cast_toNat] at h; (try push_cast at h ⊢); linear_combination (norm := parley_norm) h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ d by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := d.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ d by parley_side)]); parley_side) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ d by parley_side)]); parley_side))); rify; linear_combination (norm := parley_norm) h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ d by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := d.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ d by parley_side)]); parley_side) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ d by parley_side)]); parley_side))); qify; linear_combination (norm := parley_norm) h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ d by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := d.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ d by parley_side)]); parley_side) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ d by parley_side)]); parley_side))); parley_int_power h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ d by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := d.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ d by parley_side)]); parley_side) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ d by parley_side)]); parley_side))); parley_side)
    -- 2.5. inequalities
    have s2_5 : d ≠ 1 := by parley_side
    all_goals parley_side
  -- 3. exhibit, from 1, 2
  have s3 : ∃ p : ℤ, ∃ q : ℤ, (q > 0 ∧ x = (p : ℚ) / (q : ℚ)) ∧ ¬ (∃ d : ℤ, (d > 1 ∧ d ∣ p) ∧ d ∣ q) := ⟨p, (q : ℤ), ⟨⟨by parley_side, by parley_side⟩, by parley_side⟩⟩
  all_goals exact s3

end Parley.Proofs.Wiedijk.Sqrt2Irrational.LowestTerms
