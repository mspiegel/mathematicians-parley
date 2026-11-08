module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.ModNatural

theorem mod_natural (a : ℤ) (b : ℤ) (hH2 : 0 < b) :
    0 ≤ a % b := by
  -- 1. mun:divisibility-mod-natural
  exact (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := a) (b := b) (by parley_side))

end Parley.Tests.Stdlib.Divisibility.ModNatural
