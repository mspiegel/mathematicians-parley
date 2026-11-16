module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Sets

/-! Written from tests/notations/pairs.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Pairs.AnIntervalAndAPair

theorem an_interval_and_a_pair (x : ℝ) (hH2 : x ∈ (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) (hH3 : ((x, (2 : ℤ)) : ℝ × ℤ) = ((1 : ℝ), (2 : ℤ))) :
    x = 1 := by
  -- 1. mun:pair-parts-equal, from H3
  have s1 : x = 1 ∧ (2 : ℤ) = 2 := by
    have hI : x = 1 ∧ (2 : ℤ) = 2 := by exact_mod_cast (((Parley.Items.Stdlib.Sets.mun_pair_parts_equal (a := (x : ℂ)) (b := (2 : ℂ)) (c := (1 : ℂ)) (d := (2 : ℂ)))).mp (by (have h := hH3; simp only [Prod.mk.injEq] at h ⊢; exact_mod_cast h)))
    exact hI
  -- 2. restate 1
  exact s1.1

end Parley.Tests.Notations.Pairs.AnIntervalAndAPair
