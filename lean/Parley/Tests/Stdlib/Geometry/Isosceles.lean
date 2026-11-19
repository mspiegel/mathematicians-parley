module

public import Geometry
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Ring.Basic
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
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry
public import Parley.Items.Stdlib.Reasoning

/-! Written from tests/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Geometry.Isosceles

theorem isosceles (P : ℂ) (Q : ℂ) (R : ℂ) (hH4 : LeanBridges.Geometry.Triangle P Q R) (hH5 : dist P Q = dist P R) :
    (LeanBridges.Geometry.Triangle P Q R ∧ (dist P Q = dist P R ∨ dist Q P = dist Q R ∨ dist R P = dist R Q)) := by
  -- 1. mun:or-left, from H5
  have s1 : dist P Q = dist P R ∨ dist Q P = dist Q R := by exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := dist P Q = dist P R) (Q := dist Q P = dist Q R) hH5)
  -- 2. mun:or-left, from 1
  have s2 : (dist P Q = dist P R ∨ dist Q P = dist Q R) ∨ dist R P = dist R Q := by exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := dist P Q = dist P R ∨ dist Q P = dist Q R) (Q := dist R P = dist R Q) s1)
  -- 3. def:geometry-isosceles, from H4, 2
  exact ((Parley.Items.Stdlib.Geometry.def_isosceles (P := P) (Q := Q) (R := R))).mpr ⟨hH4, s2⟩

end Parley.Tests.Stdlib.Geometry.Isosceles
