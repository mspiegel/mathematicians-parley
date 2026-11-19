module

public import Geometry
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Geometry
public import Parley.Stdlib.Geometry.OnLineOther

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.OffLineOther

theorem off_line_other (A : ℂ) (B : ℂ) (X : ℂ) (Y : ℂ) (O : ℂ) (hH6 : A ≠ B) (hH7 : X ≠ Y) (hH8 : X ∈ LeanBridges.Geometry.line A B) (hH9 : Y ∈ LeanBridges.Geometry.line A B) (hH10 : ¬ O ∈ LeanBridges.Geometry.line A B) :
    ¬ O ∈ LeanBridges.Geometry.line X Y := by
  -- 1. mun:on-line-ends, from H6
  have s1a : A ∈ LeanBridges.Geometry.line A B := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := A) (B := B) hH6)
  have s1b : B ∈ LeanBridges.Geometry.line A B := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := A) (B := B) hH6)
  -- 2. contradiction
  intro hS
  -- 2.1. mun:on-line-other Z := A, from H6, H7, H8, H9, 1
  have s2_1 : A ∈ LeanBridges.Geometry.line X Y := by exact (Parley.Stdlib.Geometry.OnLineOther.on_line_other (A := A) (B := B) (X := X) (Y := Y) (Z := A) hH6 hH7 hH8 hH9 s1a)
  -- 2.2. mun:on-line-other Z := B, from H6, H7, H8, H9, 1
  have s2_2 : B ∈ LeanBridges.Geometry.line X Y := by exact (Parley.Stdlib.Geometry.OnLineOther.on_line_other (A := A) (B := B) (X := X) (Y := Y) (Z := B) hH6 hH7 hH8 hH9 s1b)
  -- 2.3. mun:on-line-other A := X, B := Y, X := A, Y := B, Z := O, from H6, H7, S, 2.1, 2.2
  have s2_3 : O ∈ LeanBridges.Geometry.line A B := by exact (Parley.Stdlib.Geometry.OnLineOther.on_line_other (A := X) (B := Y) (X := A) (Y := B) (Z := O) hH7 hH6 s2_1 s2_2 hS)
  -- 2.4. restate H10
  have s2_4 : ¬ O ∈ LeanBridges.Geometry.line A B := by exact hH10
  exact s2_4 s2_3

end Parley.Stdlib.Geometry.OffLineOther
