module

public import ArithTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Reasoning

/-! Written from tests/notations/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Divisibility.ZeroDoesNotDivideFive

theorem zero_does_not_divide_five :
    ¬ (0 : ℤ) ∣ (5 : ℤ) := by
  -- 1. mun:zero-divides n := 5
  have s1 : (0 : ℤ) ∣ (5 : ℤ) ↔ (5 : ℤ) = 0 := by first | exact (Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := (5 : ℤ))) | exact ((Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := (5 : ℤ)))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := (5 : ℤ))) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := (5 : ℤ))) | (have h := (Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := (5 : ℤ))); parley_side)
  -- 2. arithmetic
  have s2 : (5 : ℤ) ≠ 0 := by parley_arith
  -- 3. mun:iff-not-from-right, from 1, 2
  have s3 : ¬ (0 : ℤ) ∣ (5 : ℤ) := by first | exact (Parley.Items.Stdlib.Reasoning.mun_iff_not_from_right (P := (0 : ℤ) ∣ (5 : ℤ)) (Q := (5 : ℤ) = 0) s1 s2) | exact ((Parley.Items.Stdlib.Reasoning.mun_iff_not_from_right (P := (0 : ℤ) ∣ (5 : ℤ)) (Q := (5 : ℤ) = 0) s1 s2)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_iff_not_from_right (P := (0 : ℤ) ∣ (5 : ℤ)) (Q := (5 : ℤ) = 0) s1 s2) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_iff_not_from_right (P := (0 : ℤ) ∣ (5 : ℤ)) (Q := (5 : ℤ) = 0) s1 s2) | (have h := (Parley.Items.Stdlib.Reasoning.mun_iff_not_from_right (P := (0 : ℤ) ∣ (5 : ℤ)) (Q := (5 : ℤ) = 0) s1 s2); parley_side)
  all_goals exact s3

end Parley.Tests.Notations.Divisibility.ZeroDoesNotDivideFive
