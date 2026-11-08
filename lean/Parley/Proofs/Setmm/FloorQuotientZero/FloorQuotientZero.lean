module

public import AlgebraTactics
public import OrderTactics
public import RealTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/floor-quotient-zero.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.FloorQuotientZero.FloorQuotientZero

theorem floor_quotient_zero (A : ℤ) (hH1 : 0 ≤ A) (B : ℤ) (hH2 : 0 < B) :
    (A < B ↔ ⌊(A : ℝ) / (B : ℝ)⌋ = 0) := by
  -- 1. algebra
  have s1 : (B : ℝ) * ((A : ℝ) / (B : ℝ)) = (A : ℝ) := by parley_ring
  -- 2. mun:quotient-nonneg x := A, y := B, from H1, H2
  have s2 : 0 ≤ (A : ℝ) / (B : ℝ) := by exact (Parley.Items.Stdlib.Numbers.mun_quotient_nonneg (x := (A : ℝ)) (y := (B : ℝ)) (by parley_side) (by parley_side))
  -- 3. both directions
  constructor
  · skip
    intro hC1
    -- 3.1. transitivity, from 1, C1
    have s3_1 : (B : ℝ) * ((A : ℝ) / (B : ℝ)) < (B : ℝ) := by parley_order
    -- 3.2. mun:less-scaled x := A/B, y := 1, c := B, from H2, 3.1
    have s3_2 : (A : ℝ) / (B : ℝ) < 1 := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := (A : ℝ) / (B : ℝ)) (y := (1 : ℝ)) (c := (B : ℝ)) (by parley_side))).mpr (by simpa only [mul_one] using s3_1) | (have h := ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := (A : ℝ) / (B : ℝ)) (y := (1 : ℝ)) (c := (B : ℝ)) (by parley_side))).mpr (by simpa only [mul_one] using s3_1); parley_side)
    -- 3.3. mun:floor-between x := A/B, k := 0, from 2, 3.2
    first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_floor_between (x := (A : ℝ) / (B : ℝ)) (k := (0 : ℤ)))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_floor_between (x := (A : ℝ) / (B : ℝ)) (k := (0 : ℤ)))).mpr (by parley_side); parley_side)
  · skip
    intro hC2
    -- 3.4. mun:floor-between x := A/B, k := 0, from C2
    have s3_4 : 0 ≤ (A : ℝ) / (B : ℝ) ∧ (A : ℝ) / (B : ℝ) < 1 := by first | exact ((Parley.Items.Stdlib.Numbers.mun_floor_between (x := (A : ℝ) / (B : ℝ)) (k := (0 : ℤ)))).mp hC2 | exact (((Parley.Items.Stdlib.Numbers.mun_floor_between (x := (A : ℝ) / (B : ℝ)) (k := (0 : ℤ)))).mp hC2).symm | simpa using ((Parley.Items.Stdlib.Numbers.mun_floor_between (x := (A : ℝ) / (B : ℝ)) (k := (0 : ℤ)))).mp hC2 | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_floor_between (x := (A : ℝ) / (B : ℝ)) (k := (0 : ℤ)))).mp hC2 | (have h := ((Parley.Items.Stdlib.Numbers.mun_floor_between (x := (A : ℝ) / (B : ℝ)) (k := (0 : ℤ)))).mp hC2; parley_rat_of_real h) | (have h := ((Parley.Items.Stdlib.Numbers.mun_floor_between (x := (A : ℝ) / (B : ℝ)) (k := (0 : ℤ)))).mp hC2; parley_side)
    -- 3.5. mun:less-scaled x := A/B, y := 1, c := B, from H2, 3.4
    have s3_5 : (B : ℝ) * ((A : ℝ) / (B : ℝ)) < (B : ℝ) := by first | linarith [((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := (A : ℝ) / (B : ℝ)) (y := (1 : ℝ)) (c := (B : ℝ)) (by parley_side))).mp s3_4.2] | (have h := ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := (A : ℝ) / (B : ℝ)) (y := (1 : ℝ)) (c := (B : ℝ)) (by parley_side))).mp s3_4.2; push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := (A : ℝ) / (B : ℝ)) (y := (1 : ℝ)) (c := (B : ℝ)) (by parley_side))).mp s3_4.2 | (have h := ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := (A : ℝ) / (B : ℝ)) (y := (1 : ℝ)) (c := (B : ℝ)) (by parley_side))).mp s3_4.2; parley_side)
    -- 3.6. transitivity, from 1, 3.5
    parley_order

end Parley.Proofs.Setmm.FloorQuotientZero.FloorQuotientZero
