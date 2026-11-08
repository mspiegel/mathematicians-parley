module

public import ArithTactics
public import Counting
public import FactorialTactics
public import Functions
public import NormTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Counting
public import Parley.Proofs.Hammack.SquareFromChoose.ChooseOne

/-! Written from proofs/hammack/square-from-choose.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SquareFromChoose.SquareFromChoose

set_option maxHeartbeats 400000 in
theorem square_from_choose (n : ℤ) (hH1 : 0 < n) :
    n ^ 2 = 2 * (LeanBridges.Counting.choose n (2 : ℤ) : ℤ) + (LeanBridges.Counting.choose n (1 : ℤ) : ℤ) := by
  -- 1. induction on m starting at 1
  have s1 : ∀ m : ℤ, 0 < m → m ^ 2 = 2 * (LeanBridges.Counting.choose m (2 : ℤ) : ℤ) + (LeanBridges.Counting.choose m (1 : ℤ) : ℤ) := by
    intro m h_m
    replace h_m : 1 ≤ m := by omega
    induction m, h_m using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. arithmetic
      have s1_1 : (1 : ℤ) < 2 := by parley_arith
      -- 1.2. def:C n := 1, k := 2, from 1.1
      have s1_2 : (LeanBridges.Counting.choose (1 : ℤ) (2 : ℤ) : ℤ) = 0 := (Parley.Items.Stdlib.Counting.def_C_3 (n := (1 : ℤ)) (by parley_side) (k := (2 : ℤ))) s1_1
      -- 1.3. thm:choose-one n := 1
      have s1_3 : (LeanBridges.Counting.choose (1 : ℤ) (1 : ℤ) : ℤ) = 1 := (Parley.Proofs.Hammack.SquareFromChoose.ChooseOne.choose_one (n := (1 : ℤ)) (by parley_side))
      -- 1.4. algebra, from 1.2, 1.3
      linear_combination (norm := parley_norm) (-2) * s1_2 + (-1) * s1_3
    | succ m hK hIH =>
      -- 1.5. thm:pascal n := m, k := 2
      have s1_5 : (LeanBridges.Counting.choose m (2 : ℤ) : ℤ) + (LeanBridges.Counting.choose m (2 - 1 : ℤ) : ℤ) = (LeanBridges.Counting.choose (m + 1) (2 : ℤ) : ℤ) := (Parley.Items.Stdlib.Counting.thm_pascal (n := m) (by parley_side) (k := (2 : ℤ)))
      -- 1.6. substitute 2 − 1 = 1 (arithmetic) into line 1.5
      have s1_6 : (LeanBridges.Counting.choose m (2 : ℤ) : ℤ) + (LeanBridges.Counting.choose m (1 : ℤ) : ℤ) = (LeanBridges.Counting.choose (m + 1) (2 : ℤ) : ℤ) := by parley_subst_at (show (2 - 1 : ℤ) = 1 by parley_side) s1_5
      -- 1.7. thm:choose-one n := m
      have s1_7 : (LeanBridges.Counting.choose m (1 : ℤ) : ℤ) = m := by exact (Parley.Proofs.Hammack.SquareFromChoose.ChooseOne.choose_one (n := m) (by parley_side))
      -- 1.8. thm:choose-one n := m + 1
      have s1_8 : (LeanBridges.Counting.choose (m + 1) (1 : ℤ) : ℤ) = m + 1 := by exact (Parley.Proofs.Hammack.SquareFromChoose.ChooseOne.choose_one (n := m + 1) (by parley_side))
      -- 1.9. algebra, from IH, 1.6, 1.7, 1.8
      linear_combination (norm := parley_norm) hIH + (2) * s1_6 + (-1) * s1_7 + (-1) * s1_8
  -- 2. instantiate m := n in line 1
  first | linear_combination (norm := parley_norm) (s1 n (by parley_side)) | (have h := (s1 n (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s1 n (by parley_side)) | exact_mod_cast ((s1 n (by parley_side))).symm | (have h := (s1 n (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); parley_int_power h) | (have h := (s1 n (by parley_side)); parley_side)

end Parley.Proofs.Hammack.SquareFromChoose.SquareFromChoose
