module

public import AlgebraTactics
public import OrderTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/constant-multiple-limit.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ConstantMultipleLimit.ConstantMultipleLimit

theorem constant_multiple_limit (a : ℤ → ℝ) (c : ℝ) (L : ℝ) (hH4 : Filter.Tendsto (fun n : ℕ => (a (n : ℤ) : ℝ)) Filter.atTop (nhds L)) :
    Filter.Tendsto (fun n : ℕ => (c * a (n : ℤ) : ℝ)) Filter.atTop (nhds (c * L)) := by
  -- 1. mun:abs-nonneg x := c
  have s1 : abs c ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (c : ℂ)))] | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (c : ℂ))); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (c : ℂ))) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (c : ℂ))); parley_side)
  -- 2. inequalities, from 1
  have s2 : abs c + 1 > 0 := by parley_order
  -- 3. inequalities
  have s3 : abs c + 1 ≠ 0 := by parley_side
  -- 4. proof
  have s4 : ∀ ε : ℝ, ε > 0 → (∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (c * a (n : ℤ) - c * L) < ε)) := by
    intro ε
    intro hA1
    -- 4.1. mun:quotient-positive x := ε, y := |c| + 1, from A1, 2
    have s4_1 : ε / (abs c + 1) > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := ε) (y := abs c + 1) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := ε) (y := abs c + 1) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := ε) (y := abs c + 1) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := ε) (y := abs c + 1) (by parley_side) (by parley_side)); parley_side)
    -- 4.2. membership
    have r39_1 : abs c + 1 ≠ 0 := by parley_side
    -- 4.3. def:tends-to, from H4
    have s4_3 : ∀ ε : ℝ, ε > 0 → (∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (a (n : ℤ) - L) < ε)) := by first | exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := L))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := L))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := L))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := L))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := L))).mp (by parley_side); parley_side)
    -- 4.4. instantiate ε := ε/(|c| + 1) in line 4.3, from 4.1, 4.2
    have s4_4 : ∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (a (n : ℤ) - L) < ε / (abs c + 1)) := by first | exact (s4_3 (ε / (abs c + 1)) (by parley_side)) | exact ((s4_3 (ε / (abs c + 1)) (by parley_side))).symm | simpa using (s4_3 (ε / (abs c + 1)) (by parley_side)) | exact_mod_cast (s4_3 (ε / (abs c + 1)) (by parley_side)) | (have h := (s4_3 (ε / (abs c + 1)) (by parley_side)); parley_side)
    -- 4.5. obtain N from line 4.4
    obtain ⟨N, s4_5a, s4_5b⟩ := s4_4
    -- 4.6. proof
    have s4_6 : ∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (c * a (n : ℤ) - c * L) < ε := by
      intro n hK2
      intro hA2
      -- 4.6.1. membership, from H1
      -- 4.6.2. mun:abs-real x := a(n) − L, from 4.6.1
      -- 4.6.3. instantiate n := n in line 4.5, from A2
      have s4_6_3 : abs (a (n : ℤ) - L) < ε / (abs c + 1) := by first | linarith [(s4_5b n (by parley_side) (by parley_side))] | (have h := (s4_5b n (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s4_5b n (by parley_side) (by parley_side)) | (have h := (s4_5b n (by parley_side) (by parley_side)); parley_side)
      -- 4.6.4. mun:abs-nonneg x := a(n) − L, from 4.6.1
      have s4_6_4 : abs (a (n : ℤ) - L) ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (a (n : ℤ) : ℂ) - (L : ℂ)))] | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (a (n : ℤ) : ℂ) - (L : ℂ))); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (a (n : ℤ) : ℂ) - (L : ℂ))) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (a (n : ℤ) : ℂ) - (L : ℂ))); parley_side)
      -- 4.6.5. mun:less-scaled x := |a(n) − L|, y := ε/(|c| + 1), c := |c| + 1, from 2, 4.6.2, 4.6.3
      have s4_6_5 : (abs c + 1) * abs (a (n : ℤ) - L) < (abs c + 1) * (ε / (abs c + 1)) := by first | linarith [((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := abs (a (n : ℤ) - L)) (y := ε / (abs c + 1)) (c := abs c + 1) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := abs (a (n : ℤ) - L)) (y := ε / (abs c + 1)) (c := abs c + 1) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := abs (a (n : ℤ) - L)) (y := ε / (abs c + 1)) (c := abs c + 1) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := abs (a (n : ℤ) - L)) (y := ε / (abs c + 1)) (c := abs c + 1) (by parley_side))).mp (by parley_side); parley_side)
      -- 4.6.6. algebra
      have r72_1 : abs c + 1 ≠ 0 := by parley_side
      have s4_6_6 : (abs c + 1) * (ε / (abs c + 1)) = ε := by parley_ring
      -- 4.6.7. algebra, from 4.6.2
      have s4_6_7 : (abs c + 1) * abs (a (n : ℤ) - L) = abs c * abs (a (n : ℤ) - L) + abs (a (n : ℤ) - L) := by parley_ring
      -- 4.6.8. mun:abs-product x := c, y := a(n) − L, from 4.6.1
      have s4_6_8 : abs (c * (a (n : ℤ) - L)) = abs c * abs (a (n : ℤ) - L) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_abs_product (x := c) (y := a (n : ℤ) - L)) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_product (x := c) (y := a (n : ℤ) - L)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_product (x := c) (y := a (n : ℤ) - L)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_abs_product (x := c) (y := a (n : ℤ) - L)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_abs_product (x := c) (y := a (n : ℤ) - L))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_product (x := c) (y := a (n : ℤ) - L)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_product (x := c) (y := a (n : ℤ) - L)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_product (x := c) (y := a (n : ℤ) - L)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_product (x := c) (y := a (n : ℤ) - L)); parley_side)
      -- 4.6.9. substitute
      have s4_6_9 : abs (c * a (n : ℤ) - c * L) = abs c * abs (a (n : ℤ) - L) := by
        have c1 : c * (a (n : ℤ) - L) = c * a (n : ℤ) - c * L := by parley_ring
        have row1 : abs (c * a (n : ℤ) - c * L) = abs c * abs (a (n : ℤ) - L) := by parley_subst_at c1 s4_6_8
        exact row1
      -- 4.6.10. inequalities
      have s4_6_10 : abs c * abs (a (n : ℤ) - L) ≤ abs c * abs (a (n : ℤ) - L) + abs (a (n : ℤ) - L) := by parley_order
      -- 4.6.11. transitivity, from 4.6.9, 4.6.10, 4.6.7, 4.6.5, 4.6.6
      have r95_2 : abs c + 1 ≠ 0 := by parley_side
      have s4_6_11 : abs (c * a (n : ℤ) - c * L) < ε := by parley_order
      all_goals parley_side
    -- 4.7. exhibit, from 4.6
    have s4_7 : ∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (c * a (n : ℤ) - c * L) < ε) := ⟨N, by parley_side, by parley_side⟩
    all_goals parley_side
  -- 5. def:tends-to L := c·L, from 4
  have s5 : Filter.Tendsto (fun n : ℕ => (c * a (n : ℤ) : ℝ)) Filter.atTop (nhds (c * L)) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => c * a n)) (L := c * L))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => c * a n)) (L := c * L))).mpr (by parley_side); parley_side)
  all_goals exact s5

end Parley.Proofs.Hammack.ConstantMultipleLimit.ConstantMultipleLimit
