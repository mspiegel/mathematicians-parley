module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Library

/-! Written from tests/docs/grammar.proof by parley build lean. -/

public section

namespace Parley.Tests.Docs.Grammar.AGcdDivides

theorem a_gcd_divides :
    (Int.gcd (4 : ℤ) (6 : ℤ) : ℤ) ∣ (4 : ℤ) := by
  -- 1. def:gcd a := 4, b := 6
  have s1 : (Int.gcd (4 : ℤ) (6 : ℤ) : ℤ) ∣ (4 : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := 4) (by parley_side) (b := 6) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := 4) (by parley_side) (b := 6) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := 4) (by parley_side) (b := 6) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := 4) (by parley_side) (b := 6) (by parley_side))
  all_goals parley_side

end Parley.Tests.Docs.Grammar.AGcdDivides
