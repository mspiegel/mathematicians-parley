module

public import Tactics

/-! Written from tests/elaborator/a-named-term-is-a-number.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ANamedTermIsANumber.ANamedTermIsANumber

theorem a_named_term_is_a_number (N : ℤ) :
    2 * N + 1 - 1 = 2 * N := by
  set M : ℤ := 2 * N + 1 with hD1
  -- 1. algebra, from D1
  have s1 : M - 1 = 2 * N := by
    try simp only [hD1] at *
    try push_cast at *
    parley_ring
  all_goals parley_side

end Parley.Tests.Elaborator.ANamedTermIsANumber.ANamedTermIsANumber
