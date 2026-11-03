module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/textbook-exercise-shapes.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.TextbookExerciseShapes.AOneDroppedFromTheMiddle

theorem a_one_dropped_from_the_middle (b : ℤ → ℝ) (k : ℤ) (j : ℕ) :
    b k * 1 ^ j * 1 ^ k = b k * 1 ^ k := by
  -- 1. mun:one-power m := j
  have s1 : (1 ^ j : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_one_power (m := (j : ℤ))) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := (j : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := (j : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_one_power (m := (j : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_one_power (m := (j : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := (j : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := (j : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := (j : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := (j : ℤ))); parley_side)
  -- 2. substitute 1^j = 1 (line 1)
  have s2 : b k * 1 ^ j * 1 ^ k = b k * 1 ^ k := by
    have s1_w : (1 ^ j : ℝ) = 1 := by have h := congrArg (fun x : ℤ => (x : ℝ)) s1; push_cast at h; linear_combination (norm := parley_norm) h
    first | parley_subst s1_w | parley_subst s1
  all_goals exact s2

end Parley.Tests.Elaborator.TextbookExerciseShapes.AOneDroppedFromTheMiddle
