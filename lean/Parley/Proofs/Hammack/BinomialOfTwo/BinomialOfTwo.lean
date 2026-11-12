module

public import ArithTactics
public import Counting
public import FactorialTactics
public import Functions
public import NormTactics
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
public import Parley.Proofs.Hammack.BinomialOfOne.BinomialOfOne

/-! Written from proofs/hammack/binomial-of-two.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo

theorem binomial_of_two (m : ℤ) (hH1 : 0 ≤ m) :
    2 * (LeanBridges.Counting.choose m (2 : ℤ) : ℤ) = m * (m - 1) := by
  -- 1. induction on j starting at 0
  have s1 : ∀ j : ℤ, 0 ≤ j → 2 * (LeanBridges.Counting.choose j (2 : ℤ) : ℤ) = j * (j - 1) := by
    intro j h_j
    replace h_j : 0 ≤ j := by omega
    induction j, h_j using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. arithmetic
      have s1_1 : (0 : ℤ) < 2 := by parley_arith
      -- 1.2. def:C n := 0, k := 2, from 1.1
      have s1_2 : (LeanBridges.Counting.choose (0 : ℤ) (2 : ℤ) : ℤ) = 0 := by exact (Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by norm_num) (k := (2 : ℤ))) s1_1
      -- 1.3. calculation
      calc 2 * (LeanBridges.Counting.choose (0 : ℤ) (2 : ℤ) : ℤ) = 2 * 0 := by (have h := congrArg (fun t : ℤ => 2 * t) s1_2; push_cast at h ⊢; all_goals exact_mod_cast h)
        _ = 0 * (0 - 1) := by norm_num
    | succ j hK hIH =>
      -- 1.4. thm:pascal n := j, k := 2
      have s1_4 : (LeanBridges.Counting.choose j (2 : ℤ) : ℤ) + (LeanBridges.Counting.choose j (2 - 1 : ℤ) : ℤ) = (LeanBridges.Counting.choose (j + 1) (2 : ℤ) : ℤ) := by exact (Parley.Items.Stdlib.Counting.thm_pascal (n := j) hK (k := (2 : ℤ)))
      -- 1.5. substitute 2 − 1 = 1 (arithmetic) into line 1.4
      have s1_5 : (LeanBridges.Counting.choose j (2 : ℤ) : ℤ) + (LeanBridges.Counting.choose j (1 : ℤ) : ℤ) = (LeanBridges.Counting.choose (j + 1) (2 : ℤ) : ℤ) := by
        have e_arith : (2 - 1 : ℤ) = 1 := by parley_arith
        (have h := Eq.subst (motive := (fun t : ℤ => (LeanBridges.Counting.choose j (2 : ℤ) : ℤ) + (LeanBridges.Counting.choose j t : ℤ) = (LeanBridges.Counting.choose (j + 1) (2 : ℤ) : ℤ))) e_arith s1_4; push_cast at h ⊢; all_goals exact_mod_cast h)
      -- 1.6. thm:binomial-of-one m := j
      have s1_6 : (LeanBridges.Counting.choose j (1 : ℤ) : ℤ) = j := by exact (Parley.Proofs.Hammack.BinomialOfOne.BinomialOfOne.binomial_of_one (m := j) hK)
      -- 1.7. algebra, from IH, 1.5, 1.6
      linear_combination (norm := parley_norm) hIH + (-2) * s1_5 + (2) * s1_6
  -- 2. instantiate j := m in line 1
  exact (s1 m hH1)

end Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo
