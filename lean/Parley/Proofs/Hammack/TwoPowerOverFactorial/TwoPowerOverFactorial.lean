module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import Tactics
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.Data.Rat.Cast.Lemmas
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Hammack.TwoPowerOverFactorial.FactorialBeatsPower

/-! Written from proofs/hammack/two-power-over-factorial.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.TwoPowerOverFactorial.TwoPowerOverFactorial

theorem two_power_over_factorial (a : ℤ → ℝ) (hH2 : ∀ n : ℤ, 0 < n → a n = 2 ^ n.toNat / (LeanBridges.Counting.factorial n : ℝ)) :
    Filter.Tendsto (fun n : ℤ => (a n : ℝ)) Filter.atTop (nhds 0) := by
  -- 1. proof
  have s1 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (a n) < ε)) := by
    intro ε
    intro hA1
    -- 1.1. inequalities
    have s1_1 : ε / 4 > 0 := by linarith only [hA1]
    -- 1.2. obtain N: thm:archimedean x := ε/4, from 1.1
    obtain ⟨N, s1_2a, s1_2b⟩ := (Parley.Items.Stdlib.Numbers.thm_archimedean (x := ε / 4) s1_1)
    -- 1.3. proof
    have s1_3 : ∀ n : ℤ, 0 < n → n ≥ N → abs (a n) < ε := by
      intro n hK2
      intro hA2
      -- 1.3.1. mun:factorial-nat
      have s1_3_1 : 0 < (LeanBridges.Counting.factorial n : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := n) (le_of_lt hK2))
      -- 1.3.2. thm:factorial-beats-power
      have s1_3_2 : n * 2 ^ n.toNat ≤ 4 * (LeanBridges.Counting.factorial n : ℤ) := by exact (Parley.Proofs.Hammack.TwoPowerOverFactorial.FactorialBeatsPower.factorial_beats_power (n := n) hK2)
      -- 1.3.3. mun:product-positive x := n, y := n!, from 1.3.1
      have r128_1 : n > 0 := by linarith only [hK2]
      have s1_3_3 : n * (LeanBridges.Counting.factorial n : ℤ) > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_product_positive (x := n) (y := (LeanBridges.Counting.factorial n : ℤ)) r128_1 s1_3_1)
      -- 1.3.4. calculation
      have s1_3_4 : 2 ^ n.toNat / (LeanBridges.Counting.factorial n : ℚ) ≤ 4 / (n : ℚ) := by
        calc 2 ^ n.toNat / (LeanBridges.Counting.factorial n : ℚ) = (n : ℚ) * 2 ^ n.toNat / ((n : ℚ) * (LeanBridges.Counting.factorial n : ℚ)) := by parley_ring
          _ ≤ 4 * (LeanBridges.Counting.factorial n : ℚ) / ((n : ℚ) * (LeanBridges.Counting.factorial n : ℚ)) := by exact (Parley.Items.Stdlib.Numbers.mun_divide_le (x := (n : ℚ) * 2 ^ n.toNat) (y := 4 * (LeanBridges.Counting.factorial n : ℚ)) (c := (n : ℚ) * (LeanBridges.Counting.factorial n : ℚ)) (by exact_mod_cast s1_3_2) (by exact_mod_cast gt_iff_lt.mp s1_3_3))
          _ = 4 / (n : ℚ) := by parley_ring
      -- 1.3.5. mun:reciprocal-order x := N, y := n, from A2
      have r138_1 : N > 0 := by linarith only [s1_2a]
      have r138_2 : n > 0 := by linarith only [hK2]
      have s1_3_5 : 1 / (n : ℚ) ≤ 1 / (N : ℚ) := by exact ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℚ)) (by exact_mod_cast gt_iff_lt.mp r138_1) (y := (n : ℚ)) (by exact_mod_cast gt_iff_lt.mp r138_2))).mp (by exact_mod_cast ge_iff_le.mp hA2)
      -- 1.3.6. inequalities
      have s1_3_6 : 4 / (n : ℚ) ≤ 4 / (N : ℚ) := by linarith only [s1_3_5, div_eq_mul_one_div (4 : ℚ) ((n : ℚ)), div_eq_mul_one_div (4 : ℚ) ((N : ℚ))]
      -- 1.3.7. inequalities
      have s1_3_7 : 4 / (N : ℝ) < ε := by linarith only [s1_2b, div_eq_mul_one_div (4 : ℝ) ((N : ℝ))]
      -- 1.3.8. mun:power-nat a := 2, m := n
      have s1_3_8 : (0 : ℤ) < 2 ^ n.toNat := by exact (Parley.Items.Stdlib.Numbers.mun_power_nat (a := (2 : ℤ)) (by norm_num) (m := n) (le_of_lt hK2))
      -- 1.3.9. mun:quotient-positive x := 2^n, y := n!, from 1.3.1
      have r156_1 : (2 ^ n.toNat : ℤ) > 0 := by linarith only [s1_3_8]
      have s1_3_9 : 2 ^ n.toNat / (LeanBridges.Counting.factorial n : ℚ) > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := (2 ^ n.toNat : ℚ)) (y := (LeanBridges.Counting.factorial n : ℚ)) (by exact_mod_cast gt_iff_lt.mp r156_1) (by exact_mod_cast gt_iff_lt.mp s1_3_1))
      -- 1.3.10. transitivity, from 1.3.9, H2
      have s1_3_10 : 0 < a n := by exact LT.lt.trans_eq (show 2 ^ n.toNat / (LeanBridges.Counting.factorial n : ℝ) > 0 by have h := (Rat.cast_lt (K := ℝ)).mpr s1_3_9; simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_zero, Rat.cast_ofNat, Rat.cast_natCast] at h; exact h) (hH2 n hK2).symm
      -- 1.3.11. inequalities
      have s1_3_11 : 0 - ε < 0 := by linarith only [hA1]
      -- 1.3.12. transitivity, from 1.3.11, 1.3.10
      have s1_3_12 : 0 - ε < a n := by exact lt_trans s1_3_11 s1_3_10
      -- 1.3.13. transitivity, from H2, 1.3.4, 1.3.6, 1.3.7
      have s1_3_13 : a n < ε := by exact lt_of_le_of_lt (le_trans (Eq.trans_le (hH2 n hK2) (show 2 ^ n.toNat / (LeanBridges.Counting.factorial n : ℝ) ≤ 4 / (n : ℝ) by have h := (Rat.cast_le (K := ℝ)).mpr s1_3_4; simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_intCast, Rat.cast_natCast] at h; exact h)) (show 4 / (n : ℝ) ≤ 4 / (N : ℝ) by have h := (Rat.cast_le (K := ℝ)).mpr s1_3_6; simp only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_intCast] at h; exact h)) s1_3_7
      -- 1.3.14. join 1.3.12, 1.3.13
      have s1_3_14 : 0 - ε < a n ∧ a n < ε := ⟨s1_3_12, s1_3_13⟩
      -- 1.3.15. mun:abs-difference-lt x := a(n), c := 0, δ := ε, from 1.3.14
      simpa only [sub_zero] using ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := a n) (c := (0 : ℝ)) (δ := ε))).mpr ⟨s1_3_14.1, by simpa only [zero_add] using s1_3_14.2⟩
    -- 1.4. exhibit, from 1.3
    exact ⟨N, s1_2a, s1_3⟩
  -- 2. def:tends-to L := 0, from 1
  exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := (0 : ℝ)))).mpr (by simpa only [sub_zero] using s1)

end Parley.Proofs.Hammack.TwoPowerOverFactorial.TwoPowerOverFactorial
