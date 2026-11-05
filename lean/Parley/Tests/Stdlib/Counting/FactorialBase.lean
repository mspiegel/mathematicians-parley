module

public import Counting
public import FactorialTactics
public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Counting

/-! Written from tests/stdlib/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Counting.FactorialBase

theorem factorial_base :
    (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) = 1 := by
  -- 1. def:factorial
  have s1 : (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) = 1 := by first | linear_combination (norm := parley_norm) Parley.Items.Stdlib.Counting.def_factorial_2 | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast Parley.Items.Stdlib.Counting.def_factorial_2 | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_2).symm | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; parley_int_power h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Counting.FactorialBase
