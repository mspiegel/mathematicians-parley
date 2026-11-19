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

namespace Parley.Stdlib.Geometry.OnLineOther

theorem on_line_other (A : ℂ) (B : ℂ) (X : ℂ) (Y : ℂ) (Z : ℂ) (hH6 : A ≠ B) (hH7 : X ≠ Y) (hH8 : X ∈ LeanBridges.Geometry.line A B) (hH9 : Y ∈ LeanBridges.Geometry.line A B) (hH10 : Z ∈ LeanBridges.Geometry.line A B) :
    Z ∈ LeanBridges.Geometry.line X Y := by
  -- 1. substitute
  have c1 : LeanBridges.Geometry.line A B = LeanBridges.Geometry.line X Y := by exact (Parley.Items.Stdlib.Geometry.axi_line_uniqueness (A := X) (B := Y) (C := A) (D := B) hH7 hH6 hH8 hH9).symm
  have row1 : Z ∈ LeanBridges.Geometry.line X Y := Eq.subst (motive := (fun t : Set ℂ => Z ∈ t)) c1 hH10
  exact row1

end Parley.Stdlib.Geometry.OnLineOther
