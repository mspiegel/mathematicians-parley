module

public import Geometry
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Geometry
public import Parley.Items.Stdlib.Reasoning
public import Parley.Stdlib.Geometry.PerpendicularFoot

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.Foot

theorem foot (P : ℂ) (Q : ℂ) (R : ℂ) (hH4 : LeanBridges.Geometry.Triangle P Q R) :
    (∃ H ∈ (Set.univ : Set ℂ), ∃ S ∈ (Set.univ : Set ℂ), ((((H ∈ LeanBridges.Geometry.line Q R ∧ S ∈ LeanBridges.Geometry.line Q R) ∧ S ≠ H) ∧ P ≠ H) ∧ P ≠ S) ∧ EuclideanGeometry.angle P H S = (90 : ℝ) * Real.pi / 180) := by
  -- 1. obtain H: thm:perpendicular-foot, from H4
  obtain ⟨H, s1a, ⟨⟨⟨s1b, s1c⟩, s1d⟩, s1e⟩⟩ := (Parley.Stdlib.Geometry.PerpendicularFoot.perpendicular_foot (P := P) (Q := Q) (R := R) hH4)
  -- 2. mun:on-line-ends A := Q, B := R, from H4
  have s2a : Q ∈ LeanBridges.Geometry.line Q R := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := Q) (B := R) hH4.2.1)
  have s2b : R ∈ LeanBridges.Geometry.line Q R := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := Q) (B := R) hH4.2.1)
  -- 3. axi:excluded-middle P := H = Q
  have s3 : H = Q ∨ H ≠ Q := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := H = Q))
  -- 4. cases, from 3
  rcases s3 with hC1 | hC2
  · skip
    -- 4.1. contradiction
    have s4_1 : H ≠ R := by
      intro hS1
      -- 4.1.1. calculation
      have s4_1_1 : Q = R := by
        calc Q = H := hC1.symm
          _ = R := hS1
      exact hH4.2.1 s4_1_1
    -- 4.2. mun:modus-ponens, from 1, 4.1
    have s4_2 : EuclideanGeometry.angle P H R = (90 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := H ≠ R) (Q := EuclideanGeometry.angle P H R = (90 : ℝ) * Real.pi / 180) s1e s4_1)
    -- 4.3. exhibit, from H4, 1, 2, 4.1, 4.2
    exact ⟨H, Set.mem_univ _, R, Set.mem_univ _, ⟨⟨⟨⟨⟨s1b, s2b⟩, Ne.symm s4_1⟩, s1c⟩, hH4.2.2.1⟩, s4_2⟩⟩
  · skip
    -- 4.4. mun:modus-ponens, from C2, 1
    have s4_4 : EuclideanGeometry.angle P H Q = (90 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := H ≠ Q) (Q := EuclideanGeometry.angle P H Q = (90 : ℝ) * Real.pi / 180) s1d hC2)
    -- 4.5. exhibit, from C2, H4, 1, 2, 4.4
    exact ⟨H, Set.mem_univ _, Q, Set.mem_univ _, ⟨⟨⟨⟨⟨s1b, s2a⟩, Ne.symm hC2⟩, s1c⟩, hH4.1⟩, s4_4⟩⟩

end Parley.Stdlib.Geometry.Foot
