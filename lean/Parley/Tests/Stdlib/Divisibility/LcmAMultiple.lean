module

public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.LcmAMultiple

theorem lcm_a_multiple (a : ℤ) (b : ℤ) :
    a ∣ (Int.lcm a b : ℤ) := by
  -- 1. def:lcm
  have s1 : a ∣ (Int.lcm a b : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.def_lcm_2 (a := a) (b := b)) | exact ((Parley.Items.Stdlib.Divisibility.def_lcm_2 (a := a) (b := b))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_lcm_2 (a := a) (b := b)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_lcm_2 (a := a) (b := b)) | (have h := (Parley.Items.Stdlib.Divisibility.def_lcm_2 (a := a) (b := b)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Divisibility.LcmAMultiple
