module

public import AlgebraTactics
public import ArithTactics
public import Counting
public import FactorialTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Counting
public import Parley.Proofs.Setmm.ChooseTwoPairs.ChooseOne

/-! Written from proofs/setmm/choose-two-pairs.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ChooseTwoPairs.ChooseTwoPairs

theorem choose_two_pairs (n : ℤ) (hH1 : 0 ≤ n) :
    n + (LeanBridges.Counting.choose n (2 : ℤ) : ℤ) = (LeanBridges.Counting.choose (n + 1) (2 : ℤ) : ℤ) := by
  -- 1. thm:pascal k := 2
  have s1 : (LeanBridges.Counting.choose n (2 : ℤ) : ℤ) + (LeanBridges.Counting.choose n (2 - 1 : ℤ) : ℤ) = (LeanBridges.Counting.choose (n + 1) (2 : ℤ) : ℤ) := by exact (Parley.Items.Stdlib.Counting.thm_pascal (n := n) hH1 (k := (2 : ℤ)))
  -- 2. substitute 2 − 1 = 1 (arithmetic) into line 1
  have s2 : (LeanBridges.Counting.choose n (2 : ℤ) : ℤ) + (LeanBridges.Counting.choose n (1 : ℤ) : ℤ) = (LeanBridges.Counting.choose (n + 1) (2 : ℤ) : ℤ) := by
    have e_arith : (2 - 1 : ℤ) = 1 := by parley_arith
    (have h := Eq.subst (motive := (fun t : ℤ => (LeanBridges.Counting.choose n (2 : ℤ) : ℤ) + (LeanBridges.Counting.choose n t : ℤ) = (LeanBridges.Counting.choose (n + 1) (2 : ℤ) : ℤ))) e_arith s1; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 3. substitute
  have s3 : (LeanBridges.Counting.choose n (2 : ℤ) : ℤ) + n = (LeanBridges.Counting.choose (n + 1) (2 : ℤ) : ℤ) := by
    have c1 : (LeanBridges.Counting.choose n (1 : ℤ) : ℤ) = n := by exact (Parley.Proofs.Setmm.ChooseTwoPairs.ChooseOne.choose_one (n := n) hH1)
    have row1 : (LeanBridges.Counting.choose n (2 : ℤ) : ℤ) + n = (LeanBridges.Counting.choose (n + 1) (2 : ℤ) : ℤ) := by (have h := Eq.subst (motive := (fun t : ℤ => (LeanBridges.Counting.choose n (2 : ℤ) : ℤ) + t = (LeanBridges.Counting.choose (n + 1) (2 : ℤ) : ℤ))) c1 s2; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact row1
  -- 4. calculation
  calc n + (LeanBridges.Counting.choose n (2 : ℤ) : ℤ) = (LeanBridges.Counting.choose n (2 : ℤ) : ℤ) + n := by parley_ring
    _ = (LeanBridges.Counting.choose (n + 1) (2 : ℤ) : ℤ) := by exact s3

end Parley.Proofs.Setmm.ChooseTwoPairs.ChooseTwoPairs
