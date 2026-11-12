module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import Functions
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Counting

/-! Written from proofs/hammack/binomial-on-the-diagonal.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.BinomialOnTheDiagonal.BinomialOnTheDiagonal

theorem binomial_on_the_diagonal (m : ℤ) (hH1 : 0 ≤ m) :
    (LeanBridges.Counting.choose m m : ℤ) = 1 := by
  -- 1. induction on j starting at 0
  have s1 : ∀ j : ℤ, 0 ≤ j → (LeanBridges.Counting.choose j j : ℤ) = 1 := by
    intro j h_j
    replace h_j : 0 ≤ j := by omega
    induction j, h_j using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. mun:binomial-zero-index n := 0
      exact (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := (0 : ℤ)) (by norm_num))
    | succ j hK hIH =>
      -- 1.2. inequalities
      have s1_2 : j < j + 1 := by linarith
      -- 1.3. def:C n := j, k := j + 1, from 1.2
      have s1_3 : (LeanBridges.Counting.choose j (j + 1) : ℤ) = 0 := by exact (Parley.Items.Stdlib.Counting.def_C_3 (n := j) hK (k := j + 1)) s1_2
      -- 1.4. thm:pascal n := j, k := j + 1
      have s1_4 : (LeanBridges.Counting.choose j (j + 1) : ℤ) + (LeanBridges.Counting.choose j (j + 1 - 1) : ℤ) = (LeanBridges.Counting.choose (j + 1) (j + 1) : ℤ) := by exact (Parley.Items.Stdlib.Counting.thm_pascal (n := j) hK (k := j + 1))
      -- 1.5. substitute
      have s1_5 : (LeanBridges.Counting.choose j (j + 1) : ℤ) + (LeanBridges.Counting.choose j j : ℤ) = (LeanBridges.Counting.choose (j + 1) (j + 1) : ℤ) := by
        have c1 : j + 1 - 1 = j := by parley_ring
        have row1 : (LeanBridges.Counting.choose j (j + 1) : ℤ) + (LeanBridges.Counting.choose j j : ℤ) = (LeanBridges.Counting.choose (j + 1) (j + 1) : ℤ) := by (have h := Eq.subst (motive := (fun t : ℤ => (LeanBridges.Counting.choose j (j + 1) : ℤ) + (LeanBridges.Counting.choose j t : ℤ) = (LeanBridges.Counting.choose (j + 1) (j + 1) : ℤ))) c1 s1_4; push_cast at h ⊢; all_goals exact_mod_cast h)
        exact row1
      -- 1.6. calculation
      calc (LeanBridges.Counting.choose (j + 1) (j + 1) : ℤ) = (LeanBridges.Counting.choose j (j + 1) : ℤ) + (LeanBridges.Counting.choose j j : ℤ) := by exact s1_5.symm
        _ = 0 + (LeanBridges.Counting.choose j j : ℤ) := by (have h := congrArg (fun t : ℤ => t + (LeanBridges.Counting.choose j j : ℤ)) s1_3; push_cast at h ⊢; all_goals exact_mod_cast h)
        _ = 0 + 1 := by (have h := congrArg (fun t : ℤ => 0 + t) hIH; push_cast at h ⊢; all_goals exact_mod_cast h)
        _ = 1 := by norm_num
  -- 2. instantiate j := m in line 1
  exact (s1 m hH1)

end Parley.Proofs.Hammack.BinomialOnTheDiagonal.BinomialOnTheDiagonal
