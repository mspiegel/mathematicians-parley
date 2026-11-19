module

public import Geometry
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
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
public import Parley.Items.Stdlib.Geometry

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.OffLineAlong

theorem off_line_along (A : ℂ) (B : ℂ) (X : ℂ) (P : ℂ) (hH5 : A ≠ B) (hH6 : X ∈ LeanBridges.Geometry.line A B) (hH7 : X ≠ A) (hH8 : ¬ P ∈ LeanBridges.Geometry.line A B) :
    ¬ P ∈ LeanBridges.Geometry.line A X := by
  -- 1. mun:on-line-ends, from H5
  have s1 : A ∈ LeanBridges.Geometry.line A B := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := A) (B := B) hH5)
  -- 2. axi:line-uniqueness B := X, C := A, D := B, from H5, H6, H7, 1
  have s2 : LeanBridges.Geometry.line A X = LeanBridges.Geometry.line A B := by exact (Parley.Items.Stdlib.Geometry.axi_line_uniqueness (A := A) (B := X) (C := A) (D := B) (Ne.symm hH7) hH5 s1 hH6)
  -- 3. substitute line AX = line AB (line 2) into H8
  exact Eq.subst (motive := (fun t : Set ℂ => ¬ P ∈ t)) s2.symm hH8

end Parley.Stdlib.Geometry.OffLineAlong
