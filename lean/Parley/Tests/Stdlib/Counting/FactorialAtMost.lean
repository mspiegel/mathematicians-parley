module

public import Counting
public import FactorialTactics
public import Tactics
public import Parley.Items.Stdlib.Counting

/-! Written from tests/stdlib/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Counting.FactorialAtMost

theorem factorial_at_most (a : ℤ) (hH1 : 0 ≤ a) (b : ℤ) (hH2 : 0 ≤ b) (hH3 : a ≤ b) :
    (LeanBridges.Counting.factorial a : ℤ) ≤ (LeanBridges.Counting.factorial b : ℤ) := by
  -- 1. mun:counting-factorial-at-most m := a, n := b, from H3
  have s1 : (LeanBridges.Counting.factorial a : ℤ) ≤ (LeanBridges.Counting.factorial b : ℤ) := by first | linarith [(Parley.Items.Stdlib.Counting.mun_factorial_at_most (m := a) (by parley_side) (n := b) (by parley_side) hH3)] | (have h := (Parley.Items.Stdlib.Counting.mun_factorial_at_most (m := a) (by parley_side) (n := b) (by parley_side) hH3); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_factorial_at_most (m := a) (by parley_side) (n := b) (by parley_side) hH3) | (have h := (Parley.Items.Stdlib.Counting.mun_factorial_at_most (m := a) (by parley_side) (n := b) (by parley_side) hH3); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Counting.FactorialAtMost
