module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Sets

/-! Written from tests/stdlib/sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Sets.DifferenceEmpty

theorem difference_empty {α : Type*} (Y : Set α) :
    Y \ ∅ = Y := by
  -- 1. mun:sets-difference-empty
  have s1 : Y \ ∅ = Y := by first | exact (Parley.Items.Stdlib.Sets.mun_difference_empty (Y := Y)) | exact ((Parley.Items.Stdlib.Sets.mun_difference_empty (Y := Y))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_difference_empty (Y := Y)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_difference_empty (Y := Y)) | (have h := (Parley.Items.Stdlib.Sets.mun_difference_empty (Y := Y)); parley_set_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Sets.DifferenceEmpty
