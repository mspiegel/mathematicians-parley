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

namespace Parley.Tests.Stdlib.Divisibility.LcmLeast

theorem lcm_least (a : ℤ) (b : ℤ) :
    (∀ k : ℤ, a ∣ k ∧ b ∣ k → (Int.lcm a b : ℤ) ∣ k) := by
  -- 1. def:lcm
  exact (Parley.Items.Stdlib.Divisibility.def_lcm_4 (a := a) (b := b))

end Parley.Tests.Stdlib.Divisibility.LcmLeast
