module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.AnOpenIntervalIsReal

theorem an_open_interval_is_real (a : ℝ) (b : ℝ) :
    (Set.Ioo a b : Set ℝ) ⊆ (Set.univ : Set ℝ) := by
  -- 1. mun:open-interval-real
  have s1 : (Set.Ioo a b : Set ℝ) ⊆ (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Calculus.mun_open_interval_real (a := a) (b := b)) | exact ((Parley.Items.Stdlib.Calculus.mun_open_interval_real (a := a) (b := b))).symm | simpa using (Parley.Items.Stdlib.Calculus.mun_open_interval_real (a := a) (b := b)) | exact_mod_cast (Parley.Items.Stdlib.Calculus.mun_open_interval_real (a := a) (b := b)) | (have h := (Parley.Items.Stdlib.Calculus.mun_open_interval_real (a := a) (b := b)); parley_set_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Calculus.AnOpenIntervalIsReal
