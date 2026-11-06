module

public import Divisibility
public import PowerTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.ModBelow

theorem mod_below (a : ℝ) (b : ℝ) (hH3 : 0 ≤ a) (hH4 : a < b) :
    LeanBridges.Divisibility.mod a b = a := by
  -- 1. mun:divisibility-mod-below, from H3, H4
  have s1 : LeanBridges.Divisibility.mod a b = a := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_mod_below (a := a) (b := b) hH3 hH4) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_below (a := a) (b := b) hH3 hH4); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_below (a := a) (b := b) hH3 hH4); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_below (a := a) (b := b) hH3 hH4) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_mod_below (a := a) (b := b) hH3 hH4)).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_below (a := a) (b := b) hH3 hH4); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_below (a := a) (b := b) hH3 hH4); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_below (a := a) (b := b) hH3 hH4); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_below (a := a) (b := b) hH3 hH4); simp (disch := positivity) only [LeanBridges.Divisibility.mod_natCast, LeanBridges.Divisibility.mod_intCast] at h ⊢; exact_mod_cast h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_below (a := a) (b := b) hH3 hH4); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Divisibility.ModBelow
