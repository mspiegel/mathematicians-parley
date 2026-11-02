module

public import Tactics

/-! Written from tests/elaborator/a-family-of-parts-by-a-define.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AFamilyOfPartsByADefine.AnInstanceWhoseConditionIsItself

theorem an_instance_whose_condition_is_itself (a : ℤ) (b : ℤ) (hH3 : ∀ k : ℤ, k = a + b → a ≤ k) :
    a ≤ a + b := by
  -- 1. instantiate k := a + b in H3
  have s1 : a ≤ a + b := by first | linarith [(hH3 (a + b) (by parley_side))] | (have h := (hH3 (a + b) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (hH3 (a + b) (by parley_side)) | (have h := (hH3 (a + b) (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Tests.Elaborator.AFamilyOfPartsByADefine.AnInstanceWhoseConditionIsItself
