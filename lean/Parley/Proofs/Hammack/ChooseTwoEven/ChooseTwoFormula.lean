module

public import AlgebraTactics
public import ArithTactics
public import Counting
public import FactorialTactics
public import Functions
public import InstanceTactics
public import NormTactics
public import PowerTactics
public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Counting
public import Parley.Proofs.Setmm.ChooseTwoPairs.ChooseTwoPairs

/-! Written from proofs/hammack/choose-two-even.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ChooseTwoEven.ChooseTwoFormula

theorem choose_two_formula (n : ℤ) (hH1 : 0 ≤ n) :
    (LeanBridges.Counting.choose n (2 : ℤ) : ℚ) = (n : ℚ) * ((n : ℚ) - 1) / 2 := by
  -- 1. induction on k starting at 0
  have s1 : ∀ k : ℤ, 0 ≤ k → (LeanBridges.Counting.choose k (2 : ℤ) : ℚ) = (k : ℚ) * ((k : ℚ) - 1) / 2 := by
    intro k h_k
    replace h_k : 0 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. arithmetic
      have s1_1 : (0 : ℤ) < 2 := by parley_arith
      -- 1.2. calculation
      have s1_2 : (LeanBridges.Counting.choose (0 : ℤ) (2 : ℤ) : ℚ) = 0 * (0 - 1) / 2 := by
        calc (LeanBridges.Counting.choose (0 : ℤ) (2 : ℤ) : ℚ) = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := (2 : ℤ))) s1_1 | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := (2 : ℤ))) s1_1; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := (2 : ℤ))) s1_1; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := (2 : ℤ))) s1_1 | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := (2 : ℤ))) s1_1).symm | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := (2 : ℤ))) s1_1; rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := (2 : ℤ))) s1_1; qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := (2 : ℤ))) s1_1; parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := (2 : ℤ))) s1_1; parley_side)
          _ = 0 * (0 - 1) / 2 := by norm_num
      (have h := s1_2; push_cast at h ⊢; all_goals exact h)
    | succ k hK hIH =>
      -- 1.3. calculation
      have s1_3 : (LeanBridges.Counting.choose (k + 1) (2 : ℤ) : ℚ) = ((k : ℚ) + 1) * ((k : ℚ) + 1 - 1) / 2 := by
        calc (LeanBridges.Counting.choose (k + 1) (2 : ℤ) : ℚ) = (k : ℚ) + (LeanBridges.Counting.choose k (2 : ℤ) : ℚ) := by
              have hI : (k : ℚ) + (LeanBridges.Counting.choose k (2 : ℤ) : ℚ) = (LeanBridges.Counting.choose (k + 1) (2 : ℤ) : ℚ) := by parley_instance_cast ((Parley.Proofs.Setmm.ChooseTwoPairs.ChooseTwoPairs.choose_two_pairs (n := k) (by parley_side)))
              exact hI.symm
          _ = (k : ℚ) + (k : ℚ) * ((k : ℚ) - 1) / 2 := by (have h := congrArg (fun t : ℚ => (k : ℚ) + t) hIH; push_cast at h ⊢; all_goals exact_mod_cast h)
          _ = ((k : ℚ) + 1) * ((k : ℚ) + 1 - 1) / 2 := by parley_ring
      (have h := s1_3; push_cast at h ⊢; all_goals exact h)
  -- 2. instantiate k := n in line 1
  exact (s1 n (by parley_side))

end Parley.Proofs.Hammack.ChooseTwoEven.ChooseTwoFormula
