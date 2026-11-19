module

public import Geometry
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Notation
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry
public import Parley.Items.Stdlib.Reasoning
public import Parley.Proofs.Wiedijk.Pythagoras.Pythagoras

/-! Written from proofs/wiedijk/law-of-cosines.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.LawOfCosines.PythagorasAtFoot

theorem pythagoras_at_foot (P : ℂ) (Q : ℂ) (H : ℂ) (hH4 : P ≠ H) (hH5 : P ≠ Q) (hH6 : H ≠ Q → EuclideanGeometry.angle P H Q = (90 : ℝ) * Real.pi / 180) :
    dist P Q ^ 2 = dist P H ^ 2 + dist H Q ^ 2 := by
  -- 1. axi:excluded-middle P := H = Q
  have s1 : H = Q ∨ H ≠ Q := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := H = Q))
  -- 2. cases, from 1
  rcases s1 with hC1 | hC2
  · skip
    -- 2.1. mun:distance-zero P := H, from C1
    have s2_1 : dist H Q = 0 := ((Parley.Items.Stdlib.Geometry.mun_distance_zero (P := H) (Q := Q))).mpr hC1
    -- 2.2. calculation
    calc dist P Q ^ 2 = dist P H ^ 2 := by (have h := congrArg (fun t : ℂ => (dist P t : ℂ) ^ 2) hC1.symm; push_cast at h ⊢; exact_mod_cast h)
      _ = dist P H ^ 2 + dist H Q ^ 2 := by linear_combination (-dist H Q) * s2_1
  · skip
    -- 2.3. mun:modus-ponens, from C2, H6
    have s2_3 : EuclideanGeometry.angle P H Q = (90 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := H ≠ Q) (Q := EuclideanGeometry.angle P H Q = (90 : ℝ) * Real.pi / 180) hH6 hC2)
    -- 2.4. mun:right-angle-triangle Q := H, R := Q, from C2, H4, H5, 2.3
    have s2_4 : LeanBridges.Geometry.Triangle P H Q := by exact (Parley.Items.Stdlib.Geometry.mun_right_angle_triangle (P := P) (Q := H) (R := Q) hH4 (Ne.symm hC2) s2_3 hH5)
    -- 2.5. thm:pythagoras A := P, B := Q, C := H, from 2.3, 2.4
    exact (by (have h := (Parley.Proofs.Wiedijk.Pythagoras.Pythagoras.pythagoras (A := P) (B := Q) (C := H) (by (have h := s2_4; rw [LeanBridges.Geometry.triangle_swap_23 P H Q] at h; exact h) : LeanBridges.Geometry.Triangle P Q H) s2_3); rw [dist_comm Q H] at h; exact h) : dist P Q ^ 2 = dist P H ^ 2 + dist H Q ^ 2)

end Parley.Proofs.Wiedijk.LawOfCosines.PythagorasAtFoot
