module

public import ArithTactics
public import Counting
public import FactorialTactics
public import Functions
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Counting

/-! Written from proofs/hammack/binomial-of-one.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.BinomialOfOne.BinomialOfOne

theorem binomial_of_one (m : ℤ) (hH1 : 0 ≤ m) :
    (LeanBridges.Counting.choose m (1 : ℤ) : ℤ) = m := by
  -- 1. induction on j starting at 0
  have s1 : ∀ j : ℤ, 0 ≤ j → (LeanBridges.Counting.choose j (1 : ℤ) : ℤ) = j := by
    intro j h_j
    replace h_j : 0 ≤ j := by omega
    induction j, h_j using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. arithmetic
      have s1_1 : (0 : ℤ) < 1 := by parley_arith
      -- 1.2. def:C n := 0, k := 1, from 1.1
      exact (Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := (1 : ℤ))) s1_1
    | succ j hK hIH =>
      -- 1.3. thm:pascal n := j, k := 1
      have s1_3 : (LeanBridges.Counting.choose j (1 : ℤ) : ℤ) + (LeanBridges.Counting.choose j (1 - 1 : ℤ) : ℤ) = (LeanBridges.Counting.choose (j + 1) (1 : ℤ) : ℤ) := by exact (Parley.Items.Stdlib.Counting.thm_pascal (n := j) (by parley_side) (k := (1 : ℤ)))
      -- 1.4. mun:binomial-zero-index n := j
      have s1_4 : (LeanBridges.Counting.choose j (0 : ℤ) : ℤ) = 1 := by exact (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := j) (by parley_side))
      -- 1.5. substitute 1 − 1 = 0 (arithmetic) into line 1.3
      have s1_5 : (LeanBridges.Counting.choose j (1 : ℤ) : ℤ) + (LeanBridges.Counting.choose j (0 : ℤ) : ℤ) = (LeanBridges.Counting.choose (j + 1) (1 : ℤ) : ℤ) := by
        have e_arith : (1 - 1 : ℤ) = 0 := by parley_arith
        (have h := Eq.subst (motive := (fun t : ℤ => (LeanBridges.Counting.choose j (1 : ℤ) : ℤ) + (LeanBridges.Counting.choose j t : ℤ) = (LeanBridges.Counting.choose (j + 1) (1 : ℤ) : ℤ))) e_arith s1_3; push_cast at h ⊢; all_goals exact_mod_cast h)
      -- 1.6. calculation
      calc (LeanBridges.Counting.choose (j + 1) (1 : ℤ) : ℤ) = (LeanBridges.Counting.choose j (1 : ℤ) : ℤ) + (LeanBridges.Counting.choose j (0 : ℤ) : ℤ) := by exact s1_5.symm
        _ = j + (LeanBridges.Counting.choose j (0 : ℤ) : ℤ) := by (have h := congrArg (fun t : ℤ => t + (LeanBridges.Counting.choose j (0 : ℤ) : ℤ)) hIH; push_cast at h ⊢; all_goals exact_mod_cast h)
        _ = j + 1 := by (have h := congrArg (fun t : ℤ => j + t) s1_4; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 2. instantiate j := m in line 1
  exact (s1 m (by parley_side))

end Parley.Proofs.Hammack.BinomialOfOne.BinomialOfOne
