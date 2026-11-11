module

public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Floor
public import Mathlib.Order.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/rounding-error.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.RoundingError.RoundingError

theorem rounding_error (A : ℝ) :
    abs ((⌊A + 1 / 2⌋ : ℝ) - A) ≤ 1 / 2 := by
  -- 1. mun:floor-integer x := A + 1/2
  -- 2. mun:floor-below x := A + 1/2
  have s2 : (⌊A + 1 / 2⌋ : ℝ) ≤ A + 1 / 2 := by exact (Parley.Items.Stdlib.Numbers.mun_floor_below (x := A + 1 / 2))
  -- 3. mun:floor-above x := A + 1/2
  have s3 : A + 1 / 2 < (⌊A + 1 / 2⌋ : ℝ) + 1 := by exact (Parley.Items.Stdlib.Numbers.mun_floor_above (x := A + 1 / 2))
  set e : ℝ := (⌊A + 1 / 2⌋ : ℝ) - A with hD1
  have hD1_kind : True := by parley_side
  -- 4. inequalities
  have s4 : (⌊A + 1 / 2⌋ : ℝ) - A ≤ 1 / 2 := by parley_order
  -- 5. transitivity, from D1, 4
  have s5 : e ≤ 1 / 2 := by parley_order
  -- 6. inequalities
  have s6 : -(1 / 2) < (⌊A + 1 / 2⌋ : ℝ) - A := by parley_order
  -- 7. transitivity, from 6, D1
  have s7 : -(1 / 2) < e := by parley_order
  -- 8. inequalities
  have s8 : -e ≤ 1 / 2 := by parley_order
  -- 9. mun:nonneg-or-neg x := e, from D1
  have s9 : e ≥ 0 ∨ e < 0 := by
    try simp only [hD1] at ⊢
    try push_cast at ⊢
    exact (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := (⌊A + 1 / 2⌋ : ℝ) - A))
  -- 10. cases, from 9
  have s10 : abs e ≤ 1 / 2 := by
    rcases s9 with hC1 | hC2
    · skip
      -- 10.1. def:abs x := e, from C1, D1
      have s10_1 : abs e = e := by
        try simp only [hD1] at ⊢
        try push_cast at ⊢
        exact (Parley.Items.Stdlib.Numbers.def_abs_1 (x := (⌊A + 1 / 2⌋ : ℝ) - A)) hC1
      -- 10.2. transitivity, from 10.1, 5
      exact Eq.trans_le s10_1 s5
    · skip
      -- 10.3. def:abs x := e, from C2, D1
      have s10_3 : abs e = -e := by
        try simp only [hD1] at ⊢
        try push_cast at ⊢
        exact (Parley.Items.Stdlib.Numbers.def_abs_2 (x := (⌊A + 1 / 2⌋ : ℝ) - A)) hC2
      -- 10.4. transitivity, from 10.3, 8
      exact Eq.trans_le s10_3 s8
  -- 11. substitute e = ⌊A + 1/2⌋ − A (D1) into line 10
  (have h := Eq.subst (motive := (fun t : ℝ => abs t ≤ 1 / 2)) hD1 s10; push_cast at h ⊢; all_goals exact_mod_cast h)

end Parley.Proofs.Setmm.RoundingError.RoundingError
