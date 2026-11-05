module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import OrderTactics
public import Tactics
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Hammack.TwoPowerOverFactorial.FactorialBeatsPower

/-! Written from proofs/hammack/two-power-over-factorial.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.TwoPowerOverFactorial.TwoPowerOverFactorial

set_option maxHeartbeats 600000 in
theorem two_power_over_factorial (a : ℤ → ℝ) (hH2 : ∀ n : ℕ, 0 < n → a (n : ℤ) = 2 ^ n / (LeanBridges.Counting.factorial (n : ℤ) : ℝ)) :
    Filter.Tendsto (fun n : ℕ => (a (n : ℤ) : ℝ)) Filter.atTop (nhds 0) := by
  -- 1. proof
  have s1 : ∀ ε : ℝ, ε > 0 → (∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (a (n : ℤ)) < ε)) := by
    intro ε
    intro hA1
    -- 1.1. inequalities
    have s1_1 : ε / 4 > 0 := by parley_order
    -- 1.2. obtain N: thm:archimedean x := ε/4, from 1.1
    obtain ⟨N, s1_2a, s1_2b⟩ := (Parley.Items.Stdlib.Numbers.thm_archimedean (x := ε / 4) (by parley_side))
    try lift N to ℕ using le_of_lt s1_2a
    -- 1.3. proof
    have s1_3 : ∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (a (n : ℤ)) < ε := by
      intro n hK2
      intro hA2
      -- 1.3.1. mun:factorial-nat
      have s1_3_1 : 0 < (LeanBridges.Counting.factorial (n : ℤ) : ℤ) := by first | exact (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := n)) | exact ((Parley.Items.Stdlib.Counting.mun_factorial_nat (n := n))).symm | simpa using (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := n)) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := n)) | (have h := (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := n)); parley_side)
      -- 1.3.2. thm:factorial-beats-power
      have s1_3_2 : (n : ℝ) * 2 ^ n ≤ 4 * (LeanBridges.Counting.factorial (n : ℤ) : ℝ) := by first | linarith [(Parley.Proofs.Hammack.TwoPowerOverFactorial.FactorialBeatsPower.factorial_beats_power (n := n) (by parley_side))] | (have h := (Parley.Proofs.Hammack.TwoPowerOverFactorial.FactorialBeatsPower.factorial_beats_power (n := n) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Hammack.TwoPowerOverFactorial.FactorialBeatsPower.factorial_beats_power (n := n) (by parley_side)) | (have h := (Parley.Proofs.Hammack.TwoPowerOverFactorial.FactorialBeatsPower.factorial_beats_power (n := n) (by parley_side)); parley_side)
      -- 1.3.3. mun:product-positive x := n, y := n!, from 1.3.1
      have r128_1 : (n : ℝ) > 0 := by parley_order
      have s1_3_3 : (n : ℝ) * (LeanBridges.Counting.factorial (n : ℤ) : ℝ) > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_product_positive (x := (n : ℝ)) (y := (LeanBridges.Counting.factorial (n : ℤ) : ℝ)) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_product_positive (x := (n : ℝ)) (y := (LeanBridges.Counting.factorial (n : ℤ) : ℝ)) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_product_positive (x := (n : ℝ)) (y := (LeanBridges.Counting.factorial (n : ℤ) : ℝ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_product_positive (x := (n : ℝ)) (y := (LeanBridges.Counting.factorial (n : ℤ) : ℝ)) (by parley_side) (by parley_side)); parley_side)
      -- 1.3.4. calculation
      have s1_3_4 : 2 ^ n / (LeanBridges.Counting.factorial (n : ℤ) : ℝ) ≤ 4 / (n : ℝ) := by
        calc 2 ^ n / (LeanBridges.Counting.factorial (n : ℤ) : ℝ) = (n : ℝ) * 2 ^ n / ((n : ℝ) * (LeanBridges.Counting.factorial (n : ℤ) : ℝ)) := by parley_ring
          _ ≤ 4 * (LeanBridges.Counting.factorial (n : ℤ) : ℝ) / ((n : ℝ) * (LeanBridges.Counting.factorial (n : ℤ) : ℝ)) := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_divide_le (x := (n : ℝ) * 2 ^ n) (y := 4 * (LeanBridges.Counting.factorial (n : ℤ) : ℝ)) (c := (n : ℝ) * (LeanBridges.Counting.factorial (n : ℤ) : ℝ)) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_divide_le (x := (n : ℝ) * 2 ^ n) (y := 4 * (LeanBridges.Counting.factorial (n : ℤ) : ℝ)) (c := (n : ℝ) * (LeanBridges.Counting.factorial (n : ℤ) : ℝ)) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_divide_le (x := (n : ℝ) * 2 ^ n) (y := 4 * (LeanBridges.Counting.factorial (n : ℤ) : ℝ)) (c := (n : ℝ) * (LeanBridges.Counting.factorial (n : ℤ) : ℝ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_divide_le (x := (n : ℝ) * 2 ^ n) (y := 4 * (LeanBridges.Counting.factorial (n : ℤ) : ℝ)) (c := (n : ℝ) * (LeanBridges.Counting.factorial (n : ℤ) : ℝ)) (by parley_side) (by parley_side)); parley_side)
          _ = 4 / (n : ℝ) := by parley_ring
      -- 1.3.5. mun:reciprocal-order x := N, y := n, from A2
      have r138_1 : (N : ℝ) > 0 := by parley_order
      have r138_2 : (n : ℝ) > 0 := by parley_order
      have s1_3_5 : 1 / (n : ℝ) ≤ 1 / (N : ℝ) := by first | linarith [((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℝ)) (by parley_side) (y := (n : ℝ)) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℝ)) (by parley_side) (y := (n : ℝ)) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℝ)) (by parley_side) (y := (n : ℝ)) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℝ)) (by parley_side) (y := (n : ℝ)) (by parley_side))).mp (by parley_side); parley_side)
      -- 1.3.6. inequalities
      have s1_3_6 : 4 / (n : ℝ) ≤ 4 / (N : ℝ) := by parley_order
      -- 1.3.7. inequalities
      have s1_3_7 : 4 / (N : ℝ) < ε := by parley_order
      -- 1.3.8. mun:power-nat a := 2, m := n
      have s1_3_8 : (0 : ℤ) < 2 ^ n := by first | exact (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 2) (by parley_side) (m := n)) | exact ((Parley.Items.Stdlib.Numbers.mun_power_nat (a := 2) (by parley_side) (m := n))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 2) (by parley_side) (m := n)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 2) (by parley_side) (m := n)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 2) (by parley_side) (m := n)); parley_side)
      -- 1.3.9. mun:quotient-positive x := 2^n, y := n!, from 1.3.1
      have r156_1 : (2 ^ n : ℝ) > 0 := by parley_order
      have s1_3_9 : 2 ^ n / (LeanBridges.Counting.factorial (n : ℤ) : ℝ) > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := (2 ^ n : ℝ)) (y := (LeanBridges.Counting.factorial (n : ℤ) : ℝ)) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := (2 ^ n : ℝ)) (y := (LeanBridges.Counting.factorial (n : ℤ) : ℝ)) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := (2 ^ n : ℝ)) (y := (LeanBridges.Counting.factorial (n : ℤ) : ℝ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := (2 ^ n : ℝ)) (y := (LeanBridges.Counting.factorial (n : ℤ) : ℝ)) (by parley_side) (by parley_side)); parley_side)
      -- 1.3.10. transitivity, from 1.3.9, H2
      have s1_3_10 : 0 < a (n : ℤ) := by have := (hH2 n (by parley_side)); parley_order
      -- 1.3.11. inequalities
      have s1_3_11 : 0 - ε < 0 := by parley_order
      -- 1.3.12. transitivity, from 1.3.11, 1.3.10
      have s1_3_12 : 0 - ε < a (n : ℤ) := by parley_order
      -- 1.3.13. transitivity, from H2, 1.3.4, 1.3.6, 1.3.7
      have s1_3_13 : a (n : ℤ) < ε := by have := (hH2 n (by parley_side)); parley_order
      -- 1.3.14. join 1.3.12, 1.3.13
      have s1_3_14 : 0 - ε < a (n : ℤ) ∧ a (n : ℤ) < ε := by parley_side
      -- 1.3.15. mun:abs-difference-lt x := a(n), c := 0, δ := ε, from 1.3.14
      have s1_3_15 : abs (a (n : ℤ)) < ε := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := a (n : ℤ)) (c := (0 : ℝ)) (δ := ε))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := a (n : ℤ)) (c := (0 : ℝ)) (δ := ε))).mpr (by parley_side); parley_side)
      all_goals parley_side
    -- 1.4. exhibit, from 1.3
    have s1_4 : ∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs (a (n : ℤ)) < ε) := ⟨N, by parley_side, by parley_side⟩
    all_goals parley_side
  -- 2. def:tends-to L := 0, from 1
  have s2 : Filter.Tendsto (fun n : ℕ => (a (n : ℤ) : ℝ)) Filter.atTop (nhds 0) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := (0 : ℝ)))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := (0 : ℝ)))).mpr (by parley_side); parley_side)
  all_goals exact s2

end Parley.Proofs.Hammack.TwoPowerOverFactorial.TwoPowerOverFactorial
