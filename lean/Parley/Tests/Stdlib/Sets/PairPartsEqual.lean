module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
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

/-! Written from tests/stdlib/sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Sets.PairPartsEqual

theorem pair_parts_equal (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) (hH5 : ((a, b) : ℝ × ℝ) = (c, d)) :
    (a = c ∧ b = d) := by
  -- 1. mun:sets-pair-parts-equal, from H5
  have s1 : a = c ∧ b = d := by
    have hI : a = c ∧ b = d := by exact_mod_cast (((Parley.Items.Stdlib.Sets.mun_pair_parts_equal (a := (a : ℂ)) (b := (b : ℂ)) (c := (c : ℂ)) (d := (d : ℂ)))).mp (by (have h := hH5; simp only [Prod.mk.injEq] at h ⊢; exact_mod_cast h)))
    exact hI
  exact ⟨(s1).1, (s1).2⟩

end Parley.Tests.Stdlib.Sets.PairPartsEqual
