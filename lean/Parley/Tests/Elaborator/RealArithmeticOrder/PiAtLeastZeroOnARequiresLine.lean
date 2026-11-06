module

public import Divisibility
public import PowerTactics
public import RealTactics
public import Tactics
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/real-arithmetic-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticOrder.PiAtLeastZeroOnARequiresLine

theorem pi_at_least_zero_on_a_requires_line (N : ℝ) (hH2 : Real.pi < N) :
    LeanBridges.Divisibility.mod Real.pi N = Real.pi := by
  -- 1. mun:mod-below a := π, b := N, from H2
  have r115_1 : 0 ≤ Real.pi := by parley_real
  have s1 : LeanBridges.Divisibility.mod Real.pi N = Real.pi := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_mod_below (a := Real.pi) (b := N) (by parley_side) hH2) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_below (a := Real.pi) (b := N) (by parley_side) hH2); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_below (a := Real.pi) (b := N) (by parley_side) hH2); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_below (a := Real.pi) (b := N) (by parley_side) hH2) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_mod_below (a := Real.pi) (b := N) (by parley_side) hH2)).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_below (a := Real.pi) (b := N) (by parley_side) hH2); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_below (a := Real.pi) (b := N) (by parley_side) hH2); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_below (a := Real.pi) (b := N) (by parley_side) hH2); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_below (a := Real.pi) (b := N) (by parley_side) hH2); simp (disch := positivity) only [LeanBridges.Divisibility.mod_natCast, LeanBridges.Divisibility.mod_intCast] at h ⊢; exact_mod_cast h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_below (a := Real.pi) (b := N) (by parley_side) hH2); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticOrder.PiAtLeastZeroOnARequiresLine
