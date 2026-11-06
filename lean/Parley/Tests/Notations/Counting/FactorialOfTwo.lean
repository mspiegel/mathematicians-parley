module

public import ArithTactics
public import Counting
public import FactorialTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Counting

/-! Written from tests/notations/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Counting.FactorialOfTwo

theorem factorial_of_two :
    (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = 2 := by
  -- 1. def:factorial
  have s1 : (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) = 1 := by first | linear_combination (norm := parley_norm) Parley.Items.Stdlib.Counting.def_factorial_2 | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast Parley.Items.Stdlib.Counting.def_factorial_2 | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_2).symm | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; parley_int_power h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; parley_side)
  -- 2. def:factorial n := 1
  have s2 : (LeanBridges.Counting.factorial (1 + 1 : ℤ) : ℤ) = (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) * (1 + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_factorial_3 (n := (1 : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := (1 : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := (1 : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_3 (n := (1 : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_factorial_3 (n := (1 : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := (1 : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := (1 : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := (1 : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := (1 : ℤ)) (by parley_side)); parley_side)
  -- 3. substitute 1! = 1 (line 1) into line 2
  have s3 : (LeanBridges.Counting.factorial (1 + 1 : ℤ) : ℤ) = 1 * (1 + 1) := by first | parley_subst_at s1 s2 | (have e_nat : LeanBridges.Counting.factorial (1 : ℤ) = 1 := by exact_mod_cast s1; parley_subst_at e_nat s2)
  -- 4. arithmetic
  have s4 : (1 + 1 : ℤ) = 2 := by parley_arith
  -- 5. substitute 1 + 1 = 2 (line 4) into line 3
  have s5 : (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = 1 * 2 := by first | parley_subst_at s4 s3 | (have e_nat : 1 + 1 = 2 := by exact_mod_cast s4; parley_subst_at e_nat s3)
  -- 6. calculation
  have s6 : (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = 2 := by
    calc (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = 1 * 2 := by parley_side
      _ = 2 := by norm_num
  all_goals exact s6

end Parley.Tests.Notations.Counting.FactorialOfTwo
