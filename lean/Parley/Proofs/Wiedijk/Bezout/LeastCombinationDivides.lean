module

public import ArithTactics
public import OrderTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/wiedijk/bezout.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Bezout.LeastCombinationDivides

theorem least_combination_divides (a : ℕ) (hH1 : 0 < a) (b : ℕ) (hH2 : 0 < b) (c : ℕ) (hH3 : 0 < c) (d : ℕ) (hH4 : 0 < d) (u : ℤ) (v : ℤ) (x₀ : ℤ) (y₀ : ℤ) (hH9 : (c : ℤ) = (a : ℤ) * u + (b : ℤ) * v) (hH10 : (d : ℤ) = (a : ℤ) * x₀ + (b : ℤ) * y₀) (hH11 : ∀ x : ℤ, ∀ y : ℤ, 0 < (a : ℤ) * x + (b : ℤ) * y → (d : ℤ) ≤ (a : ℤ) * x + (b : ℤ) * y) :
    (d : ℤ) ∣ (c : ℤ) := by
  -- 1. obtain q, r: thm:division-algorithm n := c
  obtain ⟨q, r, ⟨⟨s1a, s1b⟩, s1c⟩⟩ := (Parley.Items.Stdlib.Divisibility.thm_division_algorithm (n := c) (by parley_side) (d := d) (by parley_side))
  -- 2. algebra, from H9, H10, 1
  have s2 : r = (a : ℤ) * (u - q * x₀) + (b : ℤ) * (v - q * y₀) := by linear_combination (norm := parley_norm) hH9 + (-q) * hH10 + (-1) * s1a
  -- 3. contradiction
  have s3 : r = 0 := by
    by_contra hc_hS
    have hS : r ≠ 0 := by parley_suppose hc_hS
    -- 3.1. mun:pos-int-nat m := r
    have r39_1 : 0 < r := by parley_order
    have s3_1 : 0 < r := by first | exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := r) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := r) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := r) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := r) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := r) (by parley_side)); parley_side)
    lift r to ℕ using s3_1.le
    -- 3.2. substitute r = a·(u − q·x₀) + b·(v − q·y₀) (line 2) into line 3.1
    have s3_2 : 0 < (a : ℤ) * (u - q * x₀) + (b : ℤ) * (v - q * y₀) := by parley_subst_at s2 s3_1
    -- 3.3. instantiate x := u − q·x₀, y := v − q·y₀ in H11, from 3.2
    have s3_3 : (d : ℤ) ≤ (a : ℤ) * (u - q * x₀) + (b : ℤ) * (v - q * y₀) := by first | linarith [(hH11 (u - q * x₀) (v - q * y₀) (by parley_side))] | (have h := (hH11 (u - q * x₀) (v - q * y₀) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (hH11 (u - q * x₀) (v - q * y₀) (by parley_side)) | (have h := (hH11 (u - q * x₀) (v - q * y₀) (by parley_side)); parley_side)
    -- 3.4. substitute r = a·(u − q·x₀) + b·(v − q·y₀) (line 2) into line 3.3
    have s3_4 : (d : ℤ) ≤ (r : ℤ) := by parley_subst_at s2 s3_3
    -- 3.5. inequalities, from 1
    have s3_5 : ¬ (d : ℤ) ≤ (r : ℤ) := by parley_side
    all_goals parley_side
  -- 4. substitute r = 0 (line 3) into line 1
  have s4 : (c : ℤ) = q * (d : ℤ) := by parley_subst_at s3 s1a
  -- 5. algebra, from 4
  have s5 : (c : ℤ) = (d : ℤ) * q := by linear_combination (norm := parley_norm) s4
  -- 6. def:divides n := c, from 5
  have s6 : (d : ℤ) ∣ (c : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (d : ℤ)) (n := (c : ℤ)))).mpr ⟨q, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (d : ℤ)) (n := (c : ℤ)))).mpr ⟨q, by parley_side⟩; parley_side)
  all_goals exact s6

end Parley.Proofs.Wiedijk.Bezout.LeastCombinationDivides
