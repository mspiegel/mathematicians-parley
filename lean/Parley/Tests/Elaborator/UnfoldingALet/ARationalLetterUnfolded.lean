module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/unfolding-a-let.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.UnfoldingALet.ARationalLetterUnfolded

theorem a_rational_letter_unfolded (A : ℚ) :
    (∃ p : ℤ, ∃ q : ℤ, 0 < q ∧ A = (p : ℚ) / (q : ℚ)) := by
  -- 1. def:rational x := A
  have s1 : ∃ p : ℤ, ∃ q : ℤ, 0 < q ∧ A = (p : ℚ) / (q : ℚ) := by first | exact ((Parley.Items.Stdlib.Numbers.def_rational (x := A))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Numbers.def_rational (x := A))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Numbers.def_rational (x := A))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_rational (x := A))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.def_rational (x := A))).mp (by parley_side); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.UnfoldingALet.ARationalLetterUnfolded
