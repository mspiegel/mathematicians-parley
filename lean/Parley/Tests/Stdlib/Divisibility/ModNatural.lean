module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.ModNatural

theorem mod_natural (a : ℤ) (b : ℤ) (hH2 : 0 < b) :
    0 ≤ a % b := by
  -- 1. mun:divisibility-mod-natural
  exact (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := a) (b := b) hH2)

end Parley.Tests.Stdlib.Divisibility.ModNatural
