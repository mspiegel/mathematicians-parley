module

public import LeanBridges
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/odd-as-sum-of-three-odds.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.OddAsSumOfThreeOdds.OddAsSumOfThreeOdds

theorem odd_as_sum_of_three_odds (n : ℤ) (hH2 : Odd n) :
    (∃ a : ℤ, ∃ b : ℤ, ∃ c : ℤ, ((Odd a ∧ Odd b) ∧ Odd c) ∧ n = a + b + c) := by
  -- 1. arithmetic
  have s1 : (1 : ℤ) = 2 * 0 + 1 := by parley_arith
  -- 2. def:odd n := 1, from 1
  have s2 : Odd (1 : ℤ) := ((Parley.Items.Stdlib.Divisibility.def_odd (n := (1 : ℤ)))).mpr ⟨(0 : ℤ), by parley_side⟩
  -- 3. arithmetic
  have s3 : (-1 : ℤ) = 2 * -1 + 1 := by parley_arith
  -- 4. def:odd n := −1, from 3
  have s4 : Odd (-1 : ℤ) := ((Parley.Items.Stdlib.Divisibility.def_odd (n := (-1 : ℤ)))).mpr ⟨(-1 : ℤ), by parley_side⟩
  -- 5. algebra
  have s5 : n = n + 1 + -1 := by parley_ring
  -- 6. exhibit, from H2, 2, 4, 5
  have s6 : ∃ a : ℤ, ∃ b : ℤ, ∃ c : ℤ, ((Odd a ∧ Odd b) ∧ Odd c) ∧ n = a + b + c := ⟨n, (1 : ℤ), (-1 : ℤ), by parley_side⟩
  all_goals parley_side

end Parley.Proofs.Hammack.OddAsSumOfThreeOdds.OddAsSumOfThreeOdds
