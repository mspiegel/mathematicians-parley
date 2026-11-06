module

public import ArithTactics
public import OrderTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers

/-! Written from corpus/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Divisibility.LeastCombinationDivides

set_option maxHeartbeats 400000 in
theorem least_combination_divides (a : ℤ) (b : ℤ) (hH2 : 0 < b) (c : ℤ) (d : ℤ) (hH4 : 0 < d) (u : ℤ) (v : ℤ) (x₀ : ℤ) (y₀ : ℤ) (hH9 : c = a * u + b * v) (hH10 : d = a * x₀ + b * y₀) (hH11 : ∀ x : ℤ, ∀ y : ℤ, 0 < a * x + b * y → d ≤ a * x + b * y) :
    d ∣ c := by
  -- 1. mun:mod-natural a := c, b := d
  have s1 : 0 ≤ c % d := by first | exact (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := c) (b := d) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := c) (b := d) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := c) (b := d) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := c) (b := d) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := c) (b := d) (by parley_side)); parley_side)
  -- 2. mun:mod-less a := c, b := d
  have s2 : c % d < d := by first | linarith [(Parley.Items.Stdlib.Divisibility.mun_mod_less (a := c) (b := d) (by parley_side))] | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := c) (b := d) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := c) (b := d) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := c) (b := d) (by parley_side)); parley_side)
  -- 3. obtain q: mun:mod-remainder a := c, m := d, r := c mod d, from 1, 2
  obtain ⟨q, s3⟩ := ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := c) (m := d) (by parley_side) (r := c % d) (by parley_side) s2)).mp (by parley_side)
  -- 4. algebra, from H9, H10, 3
  have s4 : c % d = a * (u - q * x₀) + b * (v - q * y₀) := by linear_combination (norm := parley_norm) hH9 + (-q) * hH10 + s3
  -- 5. contradiction
  have s5 : c % d = 0 := by
    by_contra hc_hS
    have hS : c % d ≠ 0 := by parley_suppose hc_hS
    -- 5.1. mun:pos-int-nat m := c mod d
    have r57_2 : 0 < c % d := by parley_order
    have s5_1 : 0 < c % d := by first | exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := c % d) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := c % d) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := c % d) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := c % d) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := c % d) (by parley_side)); parley_side)
    -- 5.2. substitute c mod d = a·(u − q·x₀) + b·(v − q·y₀) (line 4) into line 5.1
    have s5_2 : 0 < a * (u - q * x₀) + b * (v - q * y₀) := by parley_subst_at s4 s5_1
    -- 5.3. instantiate x := u − q·x₀, y := v − q·y₀ in H11, from 5.2
    have s5_3 : d ≤ a * (u - q * x₀) + b * (v - q * y₀) := by first | linarith [(hH11 (u - q * x₀) (v - q * y₀) (by parley_side))] | (have h := (hH11 (u - q * x₀) (v - q * y₀) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (hH11 (u - q * x₀) (v - q * y₀) (by parley_side)) | (have h := (hH11 (u - q * x₀) (v - q * y₀) (by parley_side)); parley_side)
    -- 5.4. substitute c mod d = a·(u − q·x₀) + b·(v − q·y₀) (line 4) into line 5.3
    have s5_4 : d ≤ c % d := by parley_subst_at s4 s5_3
    -- 5.5. inequalities, from 2
    have s5_5 : ¬ d ≤ c % d := by parley_side
    all_goals parley_side
  -- 6. algebra, from 3, 5
  have s6 : c = d * q := by linear_combination (norm := parley_norm) (-1) * s3 + s5
  -- 7. def:divides n := c, from 6
  have s7 : d ∣ c := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := d) (n := c))).mpr ⟨q, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := d) (n := c))).mpr ⟨q, by parley_side⟩; parley_side)
  all_goals exact s7

end Parley.Stdlib.Divisibility.LeastCombinationDivides
