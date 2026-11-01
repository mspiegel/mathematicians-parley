module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Library

/-! Written from proofs/hammack/seven-divides-four-times.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SevenDividesFourTimes.SevenDividesFourTimes

theorem seven_divides_four_times (a : ℤ) (H2 : (7 : ℤ) ∣ 4 * a) :
    (7 : ℤ) ∣ a := by
  -- 1. obtain k: def:divides d := 7, n := 4a, from H2
  obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (7 : ℤ)) (n := 4 * a))).mp (by parley_side)
  -- 2. algebra, from 1
  have s2 : a = 7 * (2 * k - a) := by linear_combination (2) * s1
  -- 3. def:divides d := 7, n := a, from 2
  have s3 : (7 : ℤ) ∣ a := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (7 : ℤ)) (n := a))).mpr ⟨2 * k - a, by parley_side⟩
  parley_side

end Parley.Proofs.Hammack.SevenDividesFourTimes.SevenDividesFourTimes
