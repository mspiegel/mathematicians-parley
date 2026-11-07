module

public import NormTactics
public import PowerTactics
public import SetTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.IntegralOverAPoint

theorem integral_over_a_point (c : ℝ) (g : ℝ → ℝ) :
    (∫ s in c..c, (g s : ℝ)) = 0 := by
  -- 1. mun:integral-point a := c, f := g
  have s1 : (∫ s in c..c, (g s : ℝ)) = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Calculus.mun_integral_point (f := g) (X := (Set.univ : Set ℝ)) (a := c)) | (have h := (Parley.Items.Stdlib.Calculus.mun_integral_point (f := g) (X := (Set.univ : Set ℝ)) (a := c)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Calculus.mun_integral_point (f := g) (X := (Set.univ : Set ℝ)) (a := c)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Calculus.mun_integral_point (f := g) (X := (Set.univ : Set ℝ)) (a := c)) | exact_mod_cast ((Parley.Items.Stdlib.Calculus.mun_integral_point (f := g) (X := (Set.univ : Set ℝ)) (a := c))).symm | (have h := (Parley.Items.Stdlib.Calculus.mun_integral_point (f := g) (X := (Set.univ : Set ℝ)) (a := c)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Calculus.mun_integral_point (f := g) (X := (Set.univ : Set ℝ)) (a := c)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Calculus.mun_integral_point (f := g) (X := (Set.univ : Set ℝ)) (a := c)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Calculus.mun_integral_point (f := g) (X := (Set.univ : Set ℝ)) (a := c)); parley_set_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Calculus.IntegralOverAPoint
