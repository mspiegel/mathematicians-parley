module

public import Tactics
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Parley.Items.Stdlib.Trigonometry

/-! Written from tests/stdlib/trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Trigonometry.CosBounded

theorem cos_bounded (a : ℝ) :
    -1 ≤ Real.cos a ∧ Real.cos a ≤ 1 := by
  -- 1. mun:trigonometry-cos-bounded
  have s1a : -1 ≤ Real.cos a := by first | linarith [(Parley.Items.Stdlib.Trigonometry.mun_cos_bounded_1 (a := a))] | (have h := (Parley.Items.Stdlib.Trigonometry.mun_cos_bounded_1 (a := a)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.mun_cos_bounded_1 (a := a)) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_cos_bounded_1 (a := a)); parley_side)
  have s1b : Real.cos a ≤ 1 := by first | linarith [(Parley.Items.Stdlib.Trigonometry.mun_cos_bounded_2 (a := a))] | (have h := (Parley.Items.Stdlib.Trigonometry.mun_cos_bounded_2 (a := a)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.mun_cos_bounded_2 (a := a)) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_cos_bounded_2 (a := a)); parley_side)
  exact ⟨by parley_side, by parley_side⟩

end Parley.Tests.Stdlib.Trigonometry.CosBounded
