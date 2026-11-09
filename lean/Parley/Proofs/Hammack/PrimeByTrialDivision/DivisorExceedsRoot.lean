module

public import AlgebraTactics
public import OrderTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/hammack/prime-by-trial-division.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.PrimeByTrialDivision.DivisorExceedsRoot

theorem divisor_exceeds_root (p : ℤ) (hH1 : 0 < p) (d : ℤ) (hH2 : 0 < d) (hH3 : 2 ≤ d) (hH4 : d ∣ p) (hH5 : ∀ n : ℤ, 0 < n → 2 ≤ n ∧ (n : ℝ) ≤ Real.sqrt (p : ℝ) → ¬ n ∣ p) :
    p < d * d := by
  -- 1. def:sqrt x := p
  have r22_1 : p ≥ 0 := by parley_order
  have s1a : Real.sqrt (p : ℝ) ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := (p : ℝ)) (by parley_side))
  have s1b : Real.sqrt (p : ℝ) ^ 2 = (p : ℝ) := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (p : ℝ)) (by parley_side))
  -- 2. contradiction
  by_contra hS
  -- 2.1. inequalities, from S
  have s2_1 : d * d ≤ p := by parley_order
  -- 2.2. calculation
  have s2_2 : (d : ℝ) ^ 2 ≤ Real.sqrt (p : ℝ) ^ 2 := by
    calc (d : ℝ) ^ 2 = (d : ℝ) * (d : ℝ) := by parley_ring
      _ ≤ (p : ℝ) := by parley_side
      _ = Real.sqrt (p : ℝ) ^ 2 := by exact s1b.symm
  -- 2.3. mun:square-le x := d, y := √p, from 1, 2.2
  have r39_1 : d ≥ 0 := by parley_order
  have s2_3 : (d : ℝ) ≤ Real.sqrt (p : ℝ) := ((Parley.Items.Stdlib.Numbers.mun_square_le (x := (d : ℝ)) (y := Real.sqrt (p : ℝ)) (by parley_side) (by parley_side))).mpr s2_2
  -- 2.4. join H3, 2.3
  have s2_4a : 2 ≤ d := by parley_side
  have s2_4b : (d : ℝ) ≤ Real.sqrt (p : ℝ) := by parley_side
  -- 2.5. instantiate n := d in H5, from H2
  have s2_5 : 2 ≤ d ∧ (d : ℝ) ≤ Real.sqrt (p : ℝ) → ¬ d ∣ p := by exact (hH5 d (by parley_side))
  -- 2.6. mun:modus-ponens P := 2 ≤ d and d ≤ √p, from 2.4, 2.5
  have s2_6 : ¬ d ∣ p := by exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := 2 ≤ d ∧ (d : ℝ) ≤ Real.sqrt (p : ℝ)) (Q := ¬ d ∣ p) s2_5 (by parley_side))
  exact s2_6 hH4

end Parley.Proofs.Hammack.PrimeByTrialDivision.DivisorExceedsRoot
