module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from tests/stdlib/sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Sets.IntersectionEmpty

theorem intersection_empty {α : Type*} (Y : Set α) :
    Y ∩ ∅ = ∅ := by
  -- 1. mun:sets-intersection-empty
  have s1 : Y ∩ ∅ = ∅ := by first | exact (Parley.Items.Stdlib.Sets.mun_intersection_empty (Y := Y)) | exact ((Parley.Items.Stdlib.Sets.mun_intersection_empty (Y := Y))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_intersection_empty (Y := Y)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_intersection_empty (Y := Y)) | (have h := (Parley.Items.Stdlib.Sets.mun_intersection_empty (Y := Y)); parley_set_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Sets.IntersectionEmpty
