module

public import AlgebraTactics
public import ArithTactics
public import InstanceTactics
public import NormTactics
public import PowerTactics
public import RealTactics
public import SubstTactics
public import Tactics
public import Batteries.Classes.RatCast
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring.RingNF
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Logarithms
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Hammack.LogThreeOverTwoIrrational.PowerOfThreeOdd
public import Parley.Proofs.Hammack.LogThreeOverTwoIrrational.PowerOfTwoEven

/-! Written from proofs/hammack/log-three-over-two-irrational.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.LogThreeOverTwoIrrational.LogThreeOverTwoIrrational

set_option maxHeartbeats 400000 in
theorem log_three_over_two_irrational :
    Irrational (Real.log (3 : ℝ) / Real.log (2 : ℝ)) := by
  -- 1. mun:quotient-positive x := ln(3), y := ln(2)
  have r90_1 : Real.log (3 : ℝ) > 0 := by parley_real
  have r90_2 : Real.log (2 : ℝ) > 0 := by parley_real
  have s1 : Real.log (3 : ℝ) / Real.log (2 : ℝ) > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := Real.log (3 : ℝ)) (y := Real.log (2 : ℝ)) (by parley_side) (by parley_side))
  -- 2. contradiction
  have s2 : ¬ (∃ m : ℚ, (m : ℝ) = Real.log (3 : ℝ) / Real.log (2 : ℝ)) := by
    intro hS
    -- 2.1. obtain p, q: def:rational x := ln(3)/ln(2), from S
    obtain ⟨p, q, s2_1a, s2_1b⟩ := ((Parley.Items.Stdlib.Numbers.def_rational (x := Real.log (3 : ℝ) / Real.log (2 : ℝ)))).mp hS
    -- 2.2. mun:product-positive x := ln(3)/ln(2), y := q, from 1, 2.1
    have r102_1 : Real.log (2 : ℝ) ≠ 0 := by parley_real
    have s2_2 : Real.log (3 : ℝ) / Real.log (2 : ℝ) * (q : ℝ) > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_product_positive (x := Real.log (3 : ℝ) / Real.log (2 : ℝ)) (y := (q : ℝ)) (by parley_side) (by parley_side))
    -- 2.3. substitute
    have r106_1 : Real.log (2 : ℝ) ≠ 0 := by parley_real
    have s2_3 : p > 0 := by
      have c1 : Real.log (3 : ℝ) / Real.log (2 : ℝ) * (q : ℝ) = (p : ℝ) := by linear_combination (norm := parley_field) ((q : ℝ)) * s2_1b
      have row1 : p > 0 := by parley_subst_at c1 s2_2
      exact row1
    -- 2.4. mun:pos-int-nat m := p, from 2.3
    have s2_4 : 0 < p := by exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := p) s2_3)
    -- 2.5. calculation
    have r115_1 : (3 : ℤ) > 0 := by parley_arith
    have r115_2 : (2 : ℤ) > 0 := by parley_arith
    have r115_3 : Real.log (2 : ℝ) ≠ 0 := by parley_real
    have s2_5 : Real.log (3 ^ q.toNat : ℝ) = Real.log (2 ^ p : ℝ) := by
      calc Real.log (3 ^ q.toNat : ℝ) = (q : ℝ) * Real.log (3 : ℝ) := by
            have hI : Real.log (3 ^ q.toNat : ℝ) = (q : ℝ) * Real.log (3 : ℝ) := by parley_instance ((Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (3 : ℝ)) (n := q) (by parley_side)))
            exact hI
        _ = (p : ℝ) * Real.log (2 : ℝ) := by linear_combination (norm := parley_field) (Real.log (2 : ℝ) * (q : ℝ)) * s2_1b
        _ = Real.log (2 ^ p : ℝ) := by exact (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (2 : ℝ)) (n := p) (by parley_side)).symm
    -- 2.6. mun:power-positive a := 3, m := q
    have r124_1 : (3 : ℤ) > 0 := by parley_arith
    have s2_6 : (3 ^ q.toNat : ℤ) > 0 := by first | (have h := (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (3 : ℚ)) (m := q) (by parley_side)); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [(Parley.Items.Stdlib.Numbers.mun_power_positive (a := (3 : ℚ)) (m := q) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (3 : ℚ)) (m := q) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (3 : ℚ)) (m := q) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (3 : ℚ)) (m := q) (by parley_side)); parley_side)
    -- 2.7. mun:power-positive a := 2, m := p
    have r128_1 : (2 : ℤ) > 0 := by parley_arith
    have s2_7 : (2 ^ p : ℚ) > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (2 : ℚ)) (m := p) (by parley_side))
    -- 2.8. calculation
    have s2_8 : (3 ^ q.toNat : ℚ) = 2 ^ p := by
      try rify
      calc (3 ^ q.toNat : ℝ) = Real.exp (Real.log (3 ^ q.toNat : ℝ)) := by exact (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := (3 ^ q.toNat : ℝ)) (by parley_side)).symm
        _ = Real.exp (Real.log (2 ^ p : ℝ)) := by parley_subst s2_5
        _ = 2 ^ p := by exact (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := (2 ^ p : ℝ)) (by parley_side))
    -- 2.9. thm:power-of-three-odd n := q
    have s2_9 : Odd (3 ^ q.toNat : ℤ) := by exact (Parley.Proofs.Hammack.LogThreeOverTwoIrrational.PowerOfThreeOdd.power_of_three_odd (n := q) (by parley_side))
    -- 2.10. thm:power-of-two-even n := p, from 2.4
    have s2_10 : ∃ m : ℤ, (m : ℚ) = (2 ^ p : ℚ) ∧ Even m := by
      have whole1 : ((2 : ℚ) : ℚ) ^ (p).toNat = (2 ^ p : ℚ) := by rw [← zpow_natCast, Int.toNat_of_nonneg (le_of_lt s2_4)]
      refine ⟨(((2 : ℤ) ^ (p).toNat) : ℤ), by first | (push_cast; simp only [whole1]; done) | (push_cast; simp only [whole1]; ring), ?_⟩
      (exact (Parley.Proofs.Hammack.LogThreeOverTwoIrrational.PowerOfTwoEven.power_of_two_even (n := p) (by parley_side)))
    -- 2.11. substitute 2^p = 3^q (line 2.8) into line 2.10
    have s2_11 : Even (3 ^ q.toNat : ℤ) := by first | parley_subst_at s2_8 s2_10 | exact parley_witness_at s2_10 ((3 ^ q.toNat : ℤ)) (by push_cast; linear_combination (norm := parley_norm) s2_8) | exact parley_witness_at s2_10 ((3 ^ q.toNat : ℤ)) (by push_cast; linear_combination (norm := parley_norm) -s2_8)
    -- 2.12. mun:odd-not-even n := 3^q, from 2.9
    have s2_12 : ¬ Even (3 ^ q.toNat : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_odd_not_even (n := (3 ^ q.toNat : ℤ)) s2_9)
    exact s2_12 s2_11
  -- 3. mun:quotient-real x := ln(3), y := ln(2)
  have r150_1 : Real.log (2 : ℝ) ≠ 0 := by parley_real
  -- 4. def:irrational x := ln(3)/ln(2), from 2, 3
  exact ((Parley.Items.Stdlib.Numbers.def_irrational (x := Real.log (3 : ℝ) / Real.log (2 : ℝ)))).mpr (by parley_side)

end Parley.Proofs.Hammack.LogThreeOverTwoIrrational.LogThreeOverTwoIrrational
