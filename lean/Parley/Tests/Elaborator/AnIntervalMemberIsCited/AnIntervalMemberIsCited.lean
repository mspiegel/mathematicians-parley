module

public import SetTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/an-interval-member-is-cited.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnIntervalMemberIsCited.AnIntervalMemberIsCited

theorem an_interval_member_is_cited (a : ℝ) (b : ℝ) (x : ℝ) (hH3 : x ∈ (Set.Ioo a b : Set ℝ)) :
    x ^ 2 ≥ 0 := by
  -- 1. mun:square-nonneg
  have s1 : x ^ 2 ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)) | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)); parley_set_side)
  all_goals exact s1

end Parley.Tests.Elaborator.AnIntervalMemberIsCited.AnIntervalMemberIsCited
