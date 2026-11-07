module

public import NormTactics
public import PowerTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Reasoning

/-! Written from tests/stdlib/reasoning.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Reasoning.IffFromLeft

theorem iff_from_left (x : ℝ) (hH2 : x = 0 ↔ x ^ 2 = 0) (hH3 : x = 0) :
    x ^ 2 = 0 := by
  -- 1. mun:reasoning-iff-from-left, from H2, H3
  have s1 : x ^ 2 = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := x = 0) (Q := x ^ 2 = 0) hH2 hH3) | (have h := (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := x = 0) (Q := x ^ 2 = 0) hH2 hH3); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := x = 0) (Q := x ^ 2 = 0) hH2 hH3); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := x = 0) (Q := x ^ 2 = 0) hH2 hH3) | exact_mod_cast ((Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := x = 0) (Q := x ^ 2 = 0) hH2 hH3)).symm | (have h := (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := x = 0) (Q := x ^ 2 = 0) hH2 hH3); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := x = 0) (Q := x ^ 2 = 0) hH2 hH3); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := x = 0) (Q := x ^ 2 = 0) hH2 hH3); parley_int_power h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := x = 0) (Q := x ^ 2 = 0) hH2 hH3); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Reasoning.IffFromLeft
