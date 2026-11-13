module

public import ArithTactics
public import Counting
public import FactorialTactics
public import NormTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Divisibility
public import Parley.Proofs.Hammack.FiveConsecutiveDivisible.ScaledBinomialStep

/-! Written from proofs/hammack/five-consecutive-divisible.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.FiveConsecutiveDivisible.FiveConsecutiveNatural

theorem five_consecutive_natural (m : ℤ) (hH1 : 0 ≤ m) :
    (120 : ℤ) ∣ (m + 1) * (m + 2) * (m + 3) * (m + 4) * (m + 5) := by
  -- 1. mun:binomial-zero-index n := m
  have s1 : (LeanBridges.Counting.choose m (0 : ℤ) : ℤ) = 1 := by exact (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := m) hH1)
  -- 2. thm:scaled-binomial-step i := 0, j := 1
  have r60_1 : (1 - 1 : ℤ) = 0 := by parley_arith
  have s2 : 1 * (LeanBridges.Counting.choose (m + 1) (1 : ℤ) : ℤ) = (m + 1) * (LeanBridges.Counting.choose m (0 : ℤ) : ℤ) := by simpa only [Int.cast_one, Int.cast_zero, add_zero, one_mul] using (Parley.Proofs.Hammack.FiveConsecutiveDivisible.ScaledBinomialStep.scaled_binomial_step (m := m) hH1 (i := (0 : ℤ)) (by norm_num) (j := (1 : ℤ)) (by norm_num) (by norm_num))
  -- 3. thm:scaled-binomial-step i := 1, j := 2
  have r64_1 : (2 - 1 : ℤ) = 1 := by parley_arith
  have s3 : 2 * (LeanBridges.Counting.choose (m + 2) (2 : ℤ) : ℤ) = (m + 2) * (LeanBridges.Counting.choose (m + 1) (1 : ℤ) : ℤ) := by exact (Parley.Proofs.Hammack.FiveConsecutiveDivisible.ScaledBinomialStep.scaled_binomial_step (m := m) hH1 (i := (1 : ℤ)) (by norm_num) (j := (2 : ℤ)) (by norm_num) (by norm_num))
  -- 4. thm:scaled-binomial-step i := 2, j := 3
  have r68_1 : (3 - 1 : ℤ) = 2 := by parley_arith
  have s4 : 3 * (LeanBridges.Counting.choose (m + 3) (3 : ℤ) : ℤ) = (m + 3) * (LeanBridges.Counting.choose (m + 2) (2 : ℤ) : ℤ) := by exact (Parley.Proofs.Hammack.FiveConsecutiveDivisible.ScaledBinomialStep.scaled_binomial_step (m := m) hH1 (i := (2 : ℤ)) (by norm_num) (j := (3 : ℤ)) (by norm_num) (by norm_num))
  -- 5. thm:scaled-binomial-step i := 3, j := 4
  have r72_1 : (4 - 1 : ℤ) = 3 := by parley_arith
  have s5 : 4 * (LeanBridges.Counting.choose (m + 4) (4 : ℤ) : ℤ) = (m + 4) * (LeanBridges.Counting.choose (m + 3) (3 : ℤ) : ℤ) := by exact (Parley.Proofs.Hammack.FiveConsecutiveDivisible.ScaledBinomialStep.scaled_binomial_step (m := m) hH1 (i := (3 : ℤ)) (by norm_num) (j := (4 : ℤ)) (by norm_num) (by norm_num))
  -- 6. thm:scaled-binomial-step i := 4, j := 5
  have r76_1 : (5 - 1 : ℤ) = 4 := by parley_arith
  have s6 : 5 * (LeanBridges.Counting.choose (m + 5) (5 : ℤ) : ℤ) = (m + 5) * (LeanBridges.Counting.choose (m + 4) (4 : ℤ) : ℤ) := by exact (Parley.Proofs.Hammack.FiveConsecutiveDivisible.ScaledBinomialStep.scaled_binomial_step (m := m) hH1 (i := (4 : ℤ)) (by norm_num) (j := (5 : ℤ)) (by norm_num) (by norm_num))
  -- 7. algebra, from 1, 2
  have s7 : (LeanBridges.Counting.choose (m + 1) (1 : ℤ) : ℤ) = m + 1 := by linear_combination (norm := parley_norm) (m + 1) * s1 + s2
  -- 8. algebra, from 3, 7
  have s8 : 2 * (LeanBridges.Counting.choose (m + 2) (2 : ℤ) : ℤ) = (m + 2) * (m + 1) := by linear_combination (norm := parley_norm) s3 + (m + 2) * s7
  -- 9. algebra, from 4, 8
  have s9 : 6 * (LeanBridges.Counting.choose (m + 3) (3 : ℤ) : ℤ) = (m + 3) * (m + 2) * (m + 1) := by linear_combination (norm := parley_norm) (2) * s4 + (m + 3) * s8
  -- 10. algebra, from 5, 9
  have s10 : 24 * (LeanBridges.Counting.choose (m + 4) (4 : ℤ) : ℤ) = (m + 4) * (m + 3) * (m + 2) * (m + 1) := by linear_combination (norm := parley_norm) (6) * s5 + (m + 4) * s9
  -- 11. algebra, from 6, 10
  have s11 : (m + 1) * (m + 2) * (m + 3) * (m + 4) * (m + 5) = 120 * (LeanBridges.Counting.choose (m + 5) (5 : ℤ) : ℤ) := by linear_combination (norm := parley_norm) (-24) * s6 + (-m - 5) * s10
  -- 12. def:divides d := 120, n := (m + 1)·(m + 2)·(m + 3)·(m + 4)·(m + 5), from 11
  exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (120 : ℤ)) (n := (m + 1) * (m + 2) * (m + 3) * (m + 4) * (m + 5)))).mpr ⟨(LeanBridges.Counting.choose (m + 5) (5 : ℤ) : ℤ), s11⟩

end Parley.Proofs.Hammack.FiveConsecutiveDivisible.FiveConsecutiveNatural
