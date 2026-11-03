module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/positive-rational-fraction.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.PositiveRationalFraction.PositiveRationalFraction

theorem positive_rational_fraction (A : ℝ) (A : ℚ) (hH3 : 0 < A) :
    (∃ x : ℕ, 0 < x ∧ (∃ y : ℕ, 0 < y ∧ A = (x : ℚ) / (y : ℚ))) := by
  -- 1. obtain p, q: def:rational x := A, from H2
  obtain ⟨p, q, s1a, s1b⟩ := ((Parley.Items.Stdlib.Numbers.def_rational (x := A))).mp (by parley_side)
  -- 2. contradiction
  have s2 : 0 < p := by
    by_contra hc_hS
    have hS : ¬ 0 < p := by parley_suppose hc_hS
    -- 2.1. inequalities, from S
    have s2_1 : p ≤ 0 := by parley_order
    -- 2.2. mun:divide-le x := p, y := 0, c := q, from 2.1
    have r24_1 : (q : ℤ) > 0 := by parley_order
    have s2_2 : (p : ℚ) / (q : ℚ) ≤ 0 / (q : ℚ) := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_divide_le (x := (p : ℚ)) (y := (0 : ℚ)) (c := (q : ℚ)) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_divide_le (x := (p : ℚ)) (y := (0 : ℚ)) (c := (q : ℚ)) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_divide_le (x := (p : ℚ)) (y := (0 : ℚ)) (c := (q : ℚ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_divide_le (x := (p : ℚ)) (y := (0 : ℚ)) (c := (q : ℚ)) (by parley_side) (by parley_side)); parley_side)
    -- 2.3. calculation
    have s2_3 : A ≤ 0 := by
      calc A = (p : ℚ) / (q : ℚ) := by parley_side
        _ ≤ 0 / (q : ℚ) := by parley_side
        _ = 0 := by parley_ring
    -- 2.4. inequalities, from H3
    have s2_4 : ¬ A ≤ 0 := by parley_side
    all_goals parley_side
  -- 3. mun:pos-int-nat m := p, from 2
  have s3 : 0 < p := by first | exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := p) s2) | exact ((Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := p) s2)).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := p) s2) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := p) s2) | (have h := (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := p) s2); parley_side)
  lift p to ℕ using s3.le
  -- 4. exhibit, from 1, 3
  have s4 : ∃ x : ℕ, 0 < x ∧ (∃ y : ℕ, 0 < y ∧ A = (x : ℚ) / (y : ℚ)) := ⟨p, by parley_side, q, by parley_side, by parley_side⟩
  all_goals exact s4

end Parley.Proofs.Setmm.PositiveRationalFraction.PositiveRationalFraction
