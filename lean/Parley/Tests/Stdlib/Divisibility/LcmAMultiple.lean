module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.LcmAMultiple

theorem lcm_a_multiple (a : ℤ) (b : ℤ) :
    a ∣ (Int.lcm a b : ℤ) := by
  -- 1. def:lcm
  exact (Parley.Items.Stdlib.Divisibility.def_lcm_2 (a := a) (b := b))

end Parley.Tests.Stdlib.Divisibility.LcmAMultiple
