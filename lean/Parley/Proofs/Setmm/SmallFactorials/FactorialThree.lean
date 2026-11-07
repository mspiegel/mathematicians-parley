module

public import ArithTactics
public import Counting
public import FactorialTactics
public import NormTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Counting
public import Parley.Proofs.Setmm.SmallFactorials.FactorialTwo

/-! Written from proofs/setmm/small-factorials.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SmallFactorials.FactorialThree

theorem factorial_three :
    (LeanBridges.Counting.factorial (3 : ℤ) : ℤ) = 6 := by
  -- 1. def:factorial n := 2
  have s1 : (LeanBridges.Counting.factorial (2 + 1 : ℤ) : ℤ) = (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) * (2 + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_factorial_3 (n := (2 : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := (2 : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := (2 : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_3 (n := (2 : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_factorial_3 (n := (2 : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := (2 : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := (2 : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := (2 : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := (2 : ℤ)) (by parley_side)); parley_side)
  -- 2. substitute
  have s2 : (LeanBridges.Counting.factorial (2 + 1 : ℤ) : ℤ) = 2 * (2 + 1) := by
    have c1 : (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = 2 := by first | linear_combination (norm := parley_norm) Parley.Proofs.Setmm.SmallFactorials.FactorialTwo.factorial_two | (have h := Parley.Proofs.Setmm.SmallFactorials.FactorialTwo.factorial_two; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Proofs.Setmm.SmallFactorials.FactorialTwo.factorial_two; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast Parley.Proofs.Setmm.SmallFactorials.FactorialTwo.factorial_two | exact_mod_cast (Parley.Proofs.Setmm.SmallFactorials.FactorialTwo.factorial_two).symm | (have h := Parley.Proofs.Setmm.SmallFactorials.FactorialTwo.factorial_two; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Proofs.Setmm.SmallFactorials.FactorialTwo.factorial_two; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Proofs.Setmm.SmallFactorials.FactorialTwo.factorial_two; parley_int_power h) | (have h := Parley.Proofs.Setmm.SmallFactorials.FactorialTwo.factorial_two; parley_side)
    have row1 : (LeanBridges.Counting.factorial (2 + 1 : ℤ) : ℤ) = 2 * (2 + 1) := by parley_subst_at c1 s1
    exact row1
  -- 3. substitute
  have s3 : (LeanBridges.Counting.factorial (3 : ℤ) : ℤ) = 2 * 3 := by
    have c1 : (2 + 1 : ℤ) = 3 := by parley_arith
    have row1 : (LeanBridges.Counting.factorial (3 : ℤ) : ℤ) = 2 * 3 := by parley_subst_at c1 s2
    exact row1
  -- 4. calculation
  have s4 : (LeanBridges.Counting.factorial (3 : ℤ) : ℤ) = 6 := by
    calc (LeanBridges.Counting.factorial (3 : ℤ) : ℤ) = 2 * 3 := by parley_side
      _ = 6 := by norm_num
  all_goals exact s4

end Parley.Proofs.Setmm.SmallFactorials.FactorialThree
