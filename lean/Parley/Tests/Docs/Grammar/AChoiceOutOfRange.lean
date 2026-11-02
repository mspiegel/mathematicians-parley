module

public import Parley.Items.Stdlib.Counting
public import Parley.Library

/-! Written from tests/docs/grammar.proof by parley build lean. -/

public section

namespace Parley.Tests.Docs.Grammar.AChoiceOutOfRange

theorem a_choice_out_of_range :
    (Parley.Library.choose (3 : ℤ) (5 : ℤ) : ℤ) = 0 := by
  -- 1. def:C n := 3, k := 5
  have r64_1 : (3 : ℤ) < 5 := by parley_arith
  have s1 : (Parley.Library.choose (3 : ℤ) (5 : ℤ) : ℤ) = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_3 (n := 3) (k := (5 : ℤ))) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 3) (k := (5 : ℤ))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_3 (n := 3) (k := (5 : ℤ))) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_3 (n := 3) (k := (5 : ℤ))) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 3) (k := (5 : ℤ))) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 3) (k := (5 : ℤ))) (by parley_side); qify; linear_combination (norm := parley_norm) h)
  all_goals parley_side

end Parley.Tests.Docs.Grammar.AChoiceOutOfRange
