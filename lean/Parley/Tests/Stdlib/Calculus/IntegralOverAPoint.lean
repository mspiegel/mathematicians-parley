module

public import PowerTactics
public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.IntegralOverAPoint

theorem integral_over_a_point (c : ℝ) (g : ℝ → ℝ) :
    (∫ s in c..c, (g s : ℝ)) = 0 := by
  -- 1. mun:integral-point a := c, f := g
  have s1 : (∫ s in c..c, (g s : ℝ)) = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Calculus.mun_integral_point (f := g) (X := (Set.univ : Set ℝ)) (a := c) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Calculus.mun_integral_point (f := g) (X := (Set.univ : Set ℝ)) (a := c) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Calculus.mun_integral_point (f := g) (X := (Set.univ : Set ℝ)) (a := c) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Calculus.mun_integral_point (f := g) (X := (Set.univ : Set ℝ)) (a := c) (by parley_set_side)) | exact_mod_cast ((Parley.Items.Stdlib.Calculus.mun_integral_point (f := g) (X := (Set.univ : Set ℝ)) (a := c) (by parley_set_side))).symm | (have h := (Parley.Items.Stdlib.Calculus.mun_integral_point (f := g) (X := (Set.univ : Set ℝ)) (a := c) (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Calculus.mun_integral_point (f := g) (X := (Set.univ : Set ℝ)) (a := c) (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Calculus.mun_integral_point (f := g) (X := (Set.univ : Set ℝ)) (a := c) (by parley_set_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Calculus.mun_integral_point (f := g) (X := (Set.univ : Set ℝ)) (a := c) (by parley_set_side)); parley_set_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Calculus.IntegralOverAPoint
