module

public import LeanBridges
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/by-name.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ByName.ValuesByName

theorem values_by_name (a : ℤ) (c : ℤ) (hH3 : c = a * 2) (hH4 : True) :
    (a ∣ c ∧ True) := by
  -- 1. def:divides n := c, d := a, from H3
  have s1 : a ∣ c := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := a) (n := c))).mpr ⟨(2 : ℤ), by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := a) (n := c))).mpr ⟨(2 : ℤ), by parley_side⟩; parley_side)
  -- 2. instantiate y := 1, x := a in H4
  -- 3. join 1, 2
  have s3 : a ∣ c ∧ True := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.ByName.ValuesByName
