module

public import ArithTactics
public import Counting
public import FactorialTactics
public import NormTactics
public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sums
public import Parley.Tests.Notations.Counting.FactorialOfFour
public import Parley.Tests.Notations.Counting.FactorialOfTwo

/-! Written from tests/notations/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Counting.ChooseFourTwo

theorem choose_four_two :
    (LeanBridges.Counting.choose (4 : ℤ) (2 : ℤ) : ℤ) = 6 := by
  -- 1. thm:factorial-of-four
  have s1 : (LeanBridges.Counting.factorial (4 : ℤ) : ℤ) = 24 := by exact Parley.Tests.Notations.Counting.FactorialOfFour.factorial_of_four
  -- 2. thm:factorial-of-two
  have s2 : (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = 2 := by exact Parley.Tests.Notations.Counting.FactorialOfTwo.factorial_of_two
  -- 3. def:C n := 4, k := 2
  have r89_1 : (0 : ℤ) ≤ 2 := by parley_arith
  have r89_2 : (2 : ℤ) ≤ 4 := by parley_arith
  have r89_3 : (2 : ℤ) ∈ Finset.Icc (0 : ℤ) (4 : ℤ) := ((Parley.Items.Stdlib.Sums.def_range_between (k := (2 : ℤ)) (a := (0 : ℤ)) (b := (4 : ℤ)))).mpr ⟨r89_1, r89_2⟩
  have s3 : (LeanBridges.Counting.choose (4 : ℤ) (2 : ℤ) : ℚ) = (LeanBridges.Counting.factorial (4 : ℤ) : ℚ) / ((LeanBridges.Counting.factorial (4 - 2 : ℤ) : ℚ) * (LeanBridges.Counting.factorial (2 : ℤ) : ℚ)) := by exact (Parley.Items.Stdlib.Counting.def_C_2 (n := (4 : ℤ)) (by norm_num) (k := (2 : ℤ))) (by parley_side)
  -- 4. arithmetic
  have s4 : (4 - 2 : ℤ) = 2 := by parley_arith
  -- 5. substitute 4 − 2 = 2 (line 4) into line 3
  have s5 : (LeanBridges.Counting.choose (4 : ℤ) (2 : ℤ) : ℚ) = (LeanBridges.Counting.factorial (4 : ℤ) : ℚ) / ((LeanBridges.Counting.factorial (2 : ℤ) : ℚ) * (LeanBridges.Counting.factorial (2 : ℤ) : ℚ)) := by (have h := Eq.subst (motive := (fun t : ℤ => (LeanBridges.Counting.choose (4 : ℤ) (2 : ℤ) : ℚ) = (LeanBridges.Counting.factorial (4 : ℤ) : ℚ) / ((LeanBridges.Counting.factorial t : ℚ) * (LeanBridges.Counting.factorial (2 : ℤ) : ℚ)))) s4 s3; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 6. substitute 4! = 24 (line 1) into line 5
  have s6 : (LeanBridges.Counting.choose (4 : ℤ) (2 : ℤ) : ℚ) = 24 / ((LeanBridges.Counting.factorial (2 : ℤ) : ℚ) * (LeanBridges.Counting.factorial (2 : ℤ) : ℚ)) := by
    have e_w : (LeanBridges.Counting.factorial (4 : ℤ) : ℚ) = 24 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s1; push_cast at h; linear_combination (norm := parley_norm) h
    (have h := Eq.subst (motive := (fun t : ℚ => (LeanBridges.Counting.choose (4 : ℤ) (2 : ℤ) : ℚ) = t / ((LeanBridges.Counting.factorial (2 : ℤ) : ℚ) * (LeanBridges.Counting.factorial (2 : ℤ) : ℚ)))) e_w s5; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 7. substitute 2! = 2 (line 2) into line 6
  have s7 : (LeanBridges.Counting.choose (4 : ℤ) (2 : ℤ) : ℚ) = 24 / (2 * 2) := by
    have e_w : (LeanBridges.Counting.factorial (2 : ℤ) : ℚ) = 2 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s2; push_cast at h; linear_combination (norm := parley_norm) h
    (have h := Eq.subst (motive := (fun t : ℚ => (LeanBridges.Counting.choose (4 : ℤ) (2 : ℤ) : ℚ) = 24 / (t * t))) e_w s6; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 8. calculation
  try qify
  calc (LeanBridges.Counting.choose (4 : ℤ) (2 : ℤ) : ℚ) = 24 / (2 * 2) := by exact s7
    _ = 6 := by norm_num

end Parley.Tests.Notations.Counting.ChooseFourTwo
