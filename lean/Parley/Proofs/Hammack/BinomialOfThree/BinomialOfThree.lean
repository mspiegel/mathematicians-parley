module

public import ArithTactics
public import Counting
public import FactorialTactics
public import Functions
public import NormTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Counting
public import Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo

/-! Written from proofs/hammack/binomial-of-three.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree

theorem binomial_of_three (m : ℤ) (hH1 : 0 ≤ m) :
    6 * (LeanBridges.Counting.choose m (3 : ℤ) : ℤ) = m * (m - 1) * (m - 2) := by
  -- 1. induction on j starting at 0
  have s1 : ∀ j : ℤ, 0 ≤ j → 6 * (LeanBridges.Counting.choose j (3 : ℤ) : ℤ) = j * (j - 1) * (j - 2) := by
    intro j h_j
    replace h_j : 0 ≤ j := by omega
    induction j, h_j using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. arithmetic
      have s1_1 : (0 : ℤ) < 3 := by parley_arith
      -- 1.2. def:C n := 0, k := 3, from 1.1
      have s1_2 : (LeanBridges.Counting.choose (0 : ℤ) (3 : ℤ) : ℤ) = 0 := (Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := (3 : ℤ))) s1_1
      -- 1.3. calculation
      calc 6 * (LeanBridges.Counting.choose (0 : ℤ) (3 : ℤ) : ℤ) = 6 * 0 := by parley_subst s1_2
        _ = 0 * (0 - 1) * (0 - 2) := by norm_num
    | succ j hK hIH =>
      -- 1.4. thm:pascal n := j, k := 3
      have s1_4 : (LeanBridges.Counting.choose j (3 : ℤ) : ℤ) + (LeanBridges.Counting.choose j (3 - 1 : ℤ) : ℤ) = (LeanBridges.Counting.choose (j + 1) (3 : ℤ) : ℤ) := (Parley.Items.Stdlib.Counting.thm_pascal (n := j) (by parley_side) (k := (3 : ℤ)))
      -- 1.5. substitute 3 − 1 = 2 (arithmetic) into line 1.4
      have s1_5 : (LeanBridges.Counting.choose j (3 : ℤ) : ℤ) + (LeanBridges.Counting.choose j (2 : ℤ) : ℤ) = (LeanBridges.Counting.choose (j + 1) (3 : ℤ) : ℤ) := by parley_subst_at (show (3 - 1 : ℤ) = 2 by parley_side) s1_4
      -- 1.6. thm:binomial-of-two m := j
      have s1_6 : 2 * (LeanBridges.Counting.choose j (2 : ℤ) : ℤ) = j * (j - 1) := by exact (Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := j) (by parley_side))
      -- 1.7. algebra, from IH, 1.5, 1.6
      linear_combination (norm := parley_norm) hIH + (-6) * s1_5 + (3) * s1_6
  -- 2. instantiate j := m in line 1
  exact (s1 m (by parley_side))

end Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree
