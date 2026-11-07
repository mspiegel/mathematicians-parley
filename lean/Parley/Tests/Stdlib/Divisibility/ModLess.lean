module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.ModLess

theorem mod_less (a : ℤ) (b : ℤ) (hH2 : 0 < b) :
    a % b < b := by
  -- 1. mun:divisibility-mod-less
  have s1 : a % b < b := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := a) (b := b) (by parley_side))
  all_goals exact s1

end Parley.Tests.Stdlib.Divisibility.ModLess
