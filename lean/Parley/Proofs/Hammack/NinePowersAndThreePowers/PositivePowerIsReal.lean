module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/nine-powers-and-three-powers.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.NinePowersAndThreePowers.PositivePowerIsReal

theorem positive_power_is_real (a : ℝ) (m : ℤ) (hH3 : a > 0) :
    True := by
  -- 1. mun:nonneg-or-neg x := m
  have s1 : m ≥ 0 ∨ m < 0 := by first | exact (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := m)) | exact ((Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := m))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := m)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := m)) | (have h := (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := m)); parley_side)
  -- 2. cases, from 1
  -- what this block shows, Lean's types give
  all_goals parley_side

end Parley.Proofs.Hammack.NinePowersAndThreePowers.PositivePowerIsReal
