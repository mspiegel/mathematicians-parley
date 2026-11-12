module

public import ArithTactics
public import Counting
public import FactorialTactics
public import Functions
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Counting

/-! Written from proofs/setmm/choose-two-pairs.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ChooseTwoPairs.ChooseOne

theorem choose_one (n : ℤ) (hH1 : 0 ≤ n) :
    (LeanBridges.Counting.choose n (1 : ℤ) : ℤ) = n := by
  -- 1. induction on k starting at 0
  have s1 : ∀ k : ℤ, 0 ≤ k → (LeanBridges.Counting.choose k (1 : ℤ) : ℤ) = k := by
    intro k h_k
    replace h_k : 0 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. arithmetic
      have s1_1 : (0 : ℤ) < 1 := by parley_arith
      -- 1.2. def:C n := 0, k := 1, from 1.1
      exact (Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by norm_num) (k := (1 : ℤ))) s1_1
    | succ k hK hIH =>
      -- 1.3. thm:pascal n := k, k := 1
      have s1_3 : (LeanBridges.Counting.choose k (1 : ℤ) : ℤ) + (LeanBridges.Counting.choose k (1 - 1 : ℤ) : ℤ) = (LeanBridges.Counting.choose (k + 1) (1 : ℤ) : ℤ) := by exact (Parley.Items.Stdlib.Counting.thm_pascal (n := k) hK (k := (1 : ℤ)))
      -- 1.4. substitute 1 − 1 = 0 (arithmetic) into line 1.3
      have s1_4 : (LeanBridges.Counting.choose k (1 : ℤ) : ℤ) + (LeanBridges.Counting.choose k (0 : ℤ) : ℤ) = (LeanBridges.Counting.choose (k + 1) (1 : ℤ) : ℤ) := by
        have e_arith : (1 - 1 : ℤ) = 0 := by parley_arith
        (have h := Eq.subst (motive := (fun t : ℤ => (LeanBridges.Counting.choose k (1 : ℤ) : ℤ) + (LeanBridges.Counting.choose k t : ℤ) = (LeanBridges.Counting.choose (k + 1) (1 : ℤ) : ℤ))) e_arith s1_3; push_cast at h ⊢; all_goals exact_mod_cast h)
      -- 1.5. substitute
      have s1_5 : (LeanBridges.Counting.choose k (1 : ℤ) : ℤ) + 1 = (LeanBridges.Counting.choose (k + 1) (1 : ℤ) : ℤ) := by
        have c1 : (LeanBridges.Counting.choose k (0 : ℤ) : ℤ) = 1 := by exact (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := k) hK)
        have row1 : (LeanBridges.Counting.choose k (1 : ℤ) : ℤ) + 1 = (LeanBridges.Counting.choose (k + 1) (1 : ℤ) : ℤ) := by (have h := Eq.subst (motive := (fun t : ℤ => (LeanBridges.Counting.choose k (1 : ℤ) : ℤ) + t = (LeanBridges.Counting.choose (k + 1) (1 : ℤ) : ℤ))) c1 s1_4; push_cast at h ⊢; all_goals exact_mod_cast h)
        exact row1
      -- 1.6. calculation
      calc (LeanBridges.Counting.choose (k + 1) (1 : ℤ) : ℤ) = (LeanBridges.Counting.choose k (1 : ℤ) : ℤ) + 1 := by exact s1_5.symm
        _ = k + 1 := by (have h := congrArg (fun t : ℤ => t + 1) hIH; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 2. instantiate k := n in line 1
  exact (s1 n hH1)

end Parley.Proofs.Setmm.ChooseTwoPairs.ChooseOne
