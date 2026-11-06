module

public import RealTactics
public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/notations/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Calculus.TheSlopeOfALine

theorem the_slope_of_a_line (g : ℝ → ℝ) (hH1 : Set.MapsTo g (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) (Set.univ : Set ℝ)) (hH2 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), g x = 2 * x) :
    (∀ x ∈ (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ), (deriv g) x = 2) := by
  -- 1. thm:derivative-linear D := [0, 1], U := (0, 1), m := 2, from H2
  have r112_1 : (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) ⊆ (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Calculus.mun_interval_real (a := (0 : ℝ)) (b := (1 : ℝ))) | exact ((Parley.Items.Stdlib.Calculus.mun_interval_real (a := (0 : ℝ)) (b := (1 : ℝ)))).symm | simpa using (Parley.Items.Stdlib.Calculus.mun_interval_real (a := (0 : ℝ)) (b := (1 : ℝ))) | exact_mod_cast (Parley.Items.Stdlib.Calculus.mun_interval_real (a := (0 : ℝ)) (b := (1 : ℝ))) | (have h := (Parley.Items.Stdlib.Calculus.mun_interval_real (a := (0 : ℝ)) (b := (1 : ℝ))); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Calculus.mun_interval_real (a := (0 : ℝ)) (b := (1 : ℝ))); parley_set_side)
  have r112_2 : (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ) ⊆ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by first | exact (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := (0 : ℝ)) (b := (1 : ℝ))) | exact ((Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := (0 : ℝ)) (b := (1 : ℝ)))).symm | simpa using (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := (0 : ℝ)) (b := (1 : ℝ))) | exact_mod_cast (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := (0 : ℝ)) (b := (1 : ℝ))) | (have h := (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := (0 : ℝ)) (b := (1 : ℝ))); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := (0 : ℝ)) (b := (1 : ℝ))); parley_set_side)
  have r112_3 : IsOpen (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ) := by first | exact (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := (0 : ℝ)) (b := (1 : ℝ))) | exact ((Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := (0 : ℝ)) (b := (1 : ℝ)))).symm | simpa using (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := (0 : ℝ)) (b := (1 : ℝ))) | exact_mod_cast (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := (0 : ℝ)) (b := (1 : ℝ))) | (have h := (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := (0 : ℝ)) (b := (1 : ℝ))); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := (0 : ℝ)) (b := (1 : ℝ))); parley_set_side)
  have s1 : ∀ x ∈ (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ), (deriv g) x = 2 := by first | exact (Parley.Items.Stdlib.Calculus.thm_derivative_linear_2 (g := g) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (U := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) (m := (2 : ℝ)) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Calculus.thm_derivative_linear_2 (g := g) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (U := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) (m := (2 : ℝ)) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Calculus.thm_derivative_linear_2 (g := g) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (U := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) (m := (2 : ℝ)) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_derivative_linear_2 (g := g) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (U := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) (m := (2 : ℝ)) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Calculus.thm_derivative_linear_2 (g := g) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (U := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) (m := (2 : ℝ)) (by parley_set_side)); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Calculus.thm_derivative_linear_2 (g := g) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (U := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) (m := (2 : ℝ)) (by parley_set_side)); parley_set_side)
  all_goals exact s1

end Parley.Tests.Notations.Calculus.TheSlopeOfALine
