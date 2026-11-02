module

public import LeanBridges
public import Parley.Tests.Notations.Primes.FloorOfMinusHalf

/-! Written from tests/notations/primes.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Primes.FloorOfMinusHalfNotZero

theorem floor_of_minus_half_not_zero :
    ⌊(-(1 / 2) : ℚ)⌋ ≠ 0 := by
  -- 1. thm:floor-of-minus-half
  have s1 : ⌊(-(1 / 2) : ℚ)⌋ = -1 := by first | linear_combination (norm := parley_norm) Parley.Tests.Notations.Primes.FloorOfMinusHalf.floor_of_minus_half | (have h := Parley.Tests.Notations.Primes.FloorOfMinusHalf.floor_of_minus_half; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast Parley.Tests.Notations.Primes.FloorOfMinusHalf.floor_of_minus_half | exact_mod_cast (Parley.Tests.Notations.Primes.FloorOfMinusHalf.floor_of_minus_half).symm | (have h := Parley.Tests.Notations.Primes.FloorOfMinusHalf.floor_of_minus_half; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Tests.Notations.Primes.FloorOfMinusHalf.floor_of_minus_half; qify; linear_combination (norm := parley_norm) h)
  -- 2. contradiction
  have s2 : ⌊(-(1 / 2) : ℚ)⌋ ≠ 0 := by
    by_contra hc_hS
    have hS : ⌊(-(1 / 2) : ℚ)⌋ = 0 := by parley_suppose hc_hS
    -- 2.1. calculation
    have s2_1 : (-1 : ℤ) = 0 := by
      calc (-1 : ℤ) = ⌊(-(1 / 2) : ℚ)⌋ := by parley_side
        _ = 0 := by parley_side
    exact absurd s2_1 (by norm_num)
    all_goals parley_side
  all_goals parley_side

end Parley.Tests.Notations.Primes.FloorOfMinusHalfNotZero
