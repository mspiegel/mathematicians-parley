module

public import Geometry
public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Operations
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.AffineSpace.Midpoint
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.Linarith.Preprocessing
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! Written from corpus/stdlib/geometry.records by parley build lean. -/

public section

namespace Parley.Items.Stdlib.Geometry

theorem def_point (A : ℂ) :
    True ↔ A ∈ (Set.univ : Set ℂ) :=
  by simp

theorem mun_angle_real_1 (P : ℂ) (Q : ℂ) (R : ℂ) (h1 : P ≠ Q) (h2 : R ≠ Q) (h3 : P ≠ R) :
    True :=
  trivial

theorem mun_angle_real_2 (P : ℂ) (Q : ℂ) (R : ℂ) (h1 : P ≠ Q) (h2 : R ≠ Q) (h3 : P ≠ R) :
    0 ≤ EuclideanGeometry.angle P Q R :=
  EuclideanGeometry.angle_nonneg P Q R

theorem mun_signed_angle_size (P : ℂ) (Q : ℂ) (R : ℂ) (h1 : P ≠ Q) (h2 : R ≠ Q) (h3 : P ≠ R) :
    abs (Complex.arg ((R - Q) / (P - Q))) = EuclideanGeometry.angle P Q R :=
  LeanBridges.Geometry.signed_angle_size P Q R h1 h2 h3

theorem mun_signed_angle_real_1 (P : ℂ) (Q : ℂ) (R : ℂ) (h1 : P ≠ Q) (h2 : R ≠ Q) :
    True :=
  trivial

theorem mun_signed_angle_real_2 (P : ℂ) (Q : ℂ) (R : ℂ) (h1 : P ≠ Q) (h2 : R ≠ Q) :
    -Real.pi < Complex.arg ((R - Q) / (P - Q)) :=
  Complex.neg_pi_lt_arg _

theorem mun_signed_angle_real_3 (P : ℂ) (Q : ℂ) (R : ℂ) (h1 : P ≠ Q) (h2 : R ≠ Q) :
    Complex.arg ((R - Q) / (P - Q)) ≤ Real.pi :=
  Complex.arg_le_pi _

theorem mun_signed_angle_reverse (P : ℂ) (Q : ℂ) (R : ℂ) (h1 : P ≠ Q) (h2 : R ≠ Q) (h3 : Complex.arg ((R - Q) / (P - Q)) ≠ Real.pi) :
    Complex.arg ((P - Q) / (R - Q)) = -Complex.arg ((R - Q) / (P - Q)) :=
  by rw [← inv_div, Complex.arg_inv, if_neg h3]

theorem thm_signed_angle_sum (P : ℂ) (Q : ℂ) (R : ℂ) (h1 : P ≠ Q) (h2 : Q ≠ R) (h3 : P ≠ R) :
    Complex.arg ((P - Q) / (R - Q)) + Complex.arg ((Q - R) / (P - R)) + Complex.arg ((R - P) / (Q - P)) ∈ ({-Real.pi, Real.pi} : Set ℝ) :=
  LeanBridges.Geometry.signed_angle_sum P Q R h1 h2 h3

theorem mun_signed_angle_zero (P : ℂ) (Q : ℂ) (h1 : P ≠ Q) :
    Complex.arg ((P - Q) / (P - Q)) = 0 :=
  by rw [div_self (sub_ne_zero.mpr h1), Complex.arg_one]

theorem mun_three_rays (A : ℂ) (B : ℂ) (Q : ℂ) (X : ℂ) (h1 : A ≠ Q) (h2 : B ≠ Q) (h3 : X ≠ Q) :
    ∃ k : ℤ, Complex.arg ((X - Q) / (A - Q)) + Complex.arg ((B - Q) / (X - Q)) = Complex.arg ((B - Q) / (A - Q)) + 2 * (k : ℝ) * Real.pi :=
  LeanBridges.Geometry.three_rays A B Q X h1 h2 h3

theorem mun_isosceles_signed_angles (A : ℂ) (B : ℂ) (Q : ℂ) (h1 : A ≠ Q) (h2 : B ≠ Q) (h3 : A ≠ B) (h4 : dist A Q = dist B Q) :
    Complex.arg ((B - A) / (Q - A)) = Complex.arg ((Q - B) / (A - B)) :=
  LeanBridges.Geometry.isosceles_signed_angles A B Q h1 h2 h3 h4

theorem mun_same_side_turns_alike (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (h1 : 0 < Complex.im ((C - A) / (B - A)) * Complex.im ((D - A) / (B - A))) :
    0 < Complex.arg ((B - C) / (A - C)) * Complex.arg ((B - D) / (A - D)) :=
  LeanBridges.Geometry.same_side_turns_alike A B C D h1

theorem def_triangle (P : ℂ) (Q : ℂ) (R : ℂ) :
    LeanBridges.Geometry.Triangle P Q R ↔ ((P ≠ Q ∧ Q ≠ R) ∧ P ≠ R) ∧ ¬ Collinear ℝ {P, Q, R} :=
  by simp only [LeanBridges.Geometry.Triangle, and_assoc]

theorem def_congruent (P : ℂ) (P' : ℂ) (Q : ℂ) (Q' : ℂ) (R : ℂ) (R' : ℂ) (h1 : LeanBridges.Geometry.Triangle P Q R) (h2 : LeanBridges.Geometry.Triangle P' Q' R') :
    dist P Q = dist P' Q' ∧ dist Q R = dist Q' R' ∧ dist R P = dist R' P' ∧ EuclideanGeometry.angle P Q R = EuclideanGeometry.angle P' Q' R' ∧ EuclideanGeometry.angle Q R P = EuclideanGeometry.angle Q' R' P' ∧ EuclideanGeometry.angle R P Q = EuclideanGeometry.angle R' P' Q' ↔ ((((dist P Q = dist P' Q' ∧ dist Q R = dist Q' R') ∧ dist R P = dist R' P') ∧ EuclideanGeometry.angle P Q R = EuclideanGeometry.angle P' Q' R') ∧ EuclideanGeometry.angle Q R P = EuclideanGeometry.angle Q' R' P') ∧ EuclideanGeometry.angle R P Q = EuclideanGeometry.angle R' P' Q' :=
  by simp only [and_assoc]

theorem def_isosceles (P : ℂ) (Q : ℂ) (R : ℂ) :
    LeanBridges.Geometry.Triangle P Q R ∧ (dist P Q = dist P R ∨ dist Q P = dist Q R ∨ dist R P = dist R Q) ↔ LeanBridges.Geometry.Triangle P Q R ∧ ((dist P Q = dist P R ∨ dist Q P = dist Q R) ∨ dist R P = dist R Q) :=
  by simp only [or_assoc]

theorem def_equilateral (P : ℂ) (Q : ℂ) (R : ℂ) :
    LeanBridges.Geometry.Triangle P Q R ∧ dist P Q = dist Q R ∧ dist Q R = dist R P ↔ (LeanBridges.Geometry.Triangle P Q R ∧ dist P Q = dist Q R) ∧ dist Q R = dist R P :=
  by simp only [and_assoc]

theorem def_right_angled (P : ℂ) (Q : ℂ) (R : ℂ) (V : ℂ) :
    LeanBridges.Geometry.Triangle P Q R ∧ (V = P ∧ EuclideanGeometry.angle Q P R = Real.pi / 2 ∨ V = Q ∧ EuclideanGeometry.angle P Q R = Real.pi / 2 ∨ V = R ∧ EuclideanGeometry.angle P R Q = Real.pi / 2) ↔ LeanBridges.Geometry.Triangle P Q R ∧ ((V = P ∧ EuclideanGeometry.angle Q P R = (90 : ℝ) * Real.pi / 180 ∨ V = Q ∧ EuclideanGeometry.angle P Q R = (90 : ℝ) * Real.pi / 180) ∨ V = R ∧ EuclideanGeometry.angle P R Q = (90 : ℝ) * Real.pi / 180) :=
  by rw [show (90 : ℝ) * Real.pi / 180 = Real.pi / 2 by ring]; simp only [or_assoc]

theorem mun_right_angled_at_vertex (P : ℂ) (Q : ℂ) (R : ℂ) :
    LeanBridges.Geometry.Triangle P Q R ∧ (R = P ∧ EuclideanGeometry.angle Q P R = Real.pi / 2 ∨ R = Q ∧ EuclideanGeometry.angle P Q R = Real.pi / 2 ∨ R = R ∧ EuclideanGeometry.angle P R Q = Real.pi / 2) ↔ LeanBridges.Geometry.Triangle P Q R ∧ EuclideanGeometry.angle P R Q = (90 : ℝ) * Real.pi / 180 :=
  LeanBridges.Geometry.right_angled_at_vertex P Q R

theorem mun_distance_symmetric (P : ℂ) (Q : ℂ) :
    dist P Q = dist Q P :=
  dist_comm P Q

theorem mun_angle_symmetric (P : ℂ) (Q : ℂ) (R : ℂ) (h1 : LeanBridges.Geometry.Triangle P Q R) :
    EuclideanGeometry.angle P Q R = EuclideanGeometry.angle R Q P :=
  EuclideanGeometry.angle_comm P Q R

theorem mun_angle_turned (P : ℂ) (Q : ℂ) (R : ℂ) (h1 : P ≠ Q) (h2 : R ≠ Q) (h3 : P ≠ R) :
    EuclideanGeometry.angle P Q R = EuclideanGeometry.angle R Q P :=
  EuclideanGeometry.angle_comm P Q R

theorem def_parallel (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (h1 : A ≠ B) (h2 : C ≠ D) :
    Complex.im ((B - A) / (D - C)) = 0 ↔ LeanBridges.Geometry.line A B = LeanBridges.Geometry.line C D ∨ ¬ (∃ X ∈ (Set.univ : Set ℂ), X ∈ LeanBridges.Geometry.line A B ∧ X ∈ LeanBridges.Geometry.line C D) :=
  LeanBridges.Geometry.parallel A B C D h1 h2

theorem def_on_line (A : ℂ) (B : ℂ) (P : ℂ) (h1 : A ≠ B) :
    P ∈ LeanBridges.Geometry.line A B ↔ Collinear ℝ {A, B, P} :=
  LeanBridges.Geometry.mem_line_iff_collinear A B P h1

theorem def_line (P : ℂ) (A : ℂ) (B : ℂ) (h1 : A ≠ B) :
    P ∈ LeanBridges.Geometry.line A B ↔ P ∈ LeanBridges.Geometry.line A B :=
  Iff.rfl

theorem def_ray (P : ℂ) (A : ℂ) (B : ℂ) (h1 : A ≠ B) :
    P ∈ LeanBridges.Geometry.ray A B ↔ ((P = A ∨ P = B) ∨ Sbtw ℝ A P B) ∨ Sbtw ℝ A B P :=
  LeanBridges.Geometry.mem_ray_iff P A B h1

theorem mun_line_turned (A : ℂ) (B : ℂ) :
    LeanBridges.Geometry.line A B = LeanBridges.Geometry.line B A :=
  LeanBridges.Geometry.line_turned A B

theorem mun_on_line_cases (P : ℂ) (Q : ℂ) (R : ℂ) (h1 : Q ≠ R) (h2 : P ∈ LeanBridges.Geometry.line Q R) :
    (((P = Q ∨ Sbtw ℝ Q P R) ∨ P = R) ∨ Sbtw ℝ Q R P) ∨ Sbtw ℝ P Q R :=
  LeanBridges.Geometry.on_line_cases P Q R h1 h2

theorem mun_perpendicular_by_right_angle (P : ℂ) (Q : ℂ) (R : ℂ) (h1 : P ≠ Q) (h2 : R ≠ Q) (h3 : P ≠ R) :
    Q ≠ P ∧ Q ≠ R ∧ Complex.re ((R - Q) / (P - Q)) = 0 ↔ EuclideanGeometry.angle P Q R = (90 : ℝ) * Real.pi / 180 :=
  LeanBridges.Geometry.perpendicular_by_right_angle P Q R h1 h2 h3

theorem def_midpoint (A : ℂ) (B : ℂ) (M : ℂ) :
    Sbtw ℝ A M B ∧ dist A M = dist M B ↔ Sbtw ℝ A M B ∧ dist A M = dist M B :=
  Iff.rfl

theorem mun_midpoint_unique (A : ℂ) (B : ℂ) (M : ℂ) (N : ℂ) (h1 : Sbtw ℝ A M B ∧ dist A M = dist M B) (h2 : Sbtw ℝ A N B ∧ dist A N = dist N B) :
    M = N :=
  LeanBridges.Geometry.midpoint_unique A B M N h1 h2

theorem mun_midpoint_determines_end (A : ℂ) (B : ℂ) (C : ℂ) (M : ℂ) (h1 : Sbtw ℝ A M B ∧ dist A M = dist M B) (h2 : Sbtw ℝ A M C ∧ dist A M = dist M C) :
    B = C :=
  LeanBridges.Geometry.midpoint_determines_end A B C M h1 h2

theorem axi_supplementary_angles (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (h1 : Sbtw ℝ A B C) (h2 : D ≠ B) (h3 : D ≠ A) (h4 : D ≠ C) :
    EuclideanGeometry.angle A B D + EuclideanGeometry.angle D B C = (180 : ℝ) * Real.pi / 180 :=
  by rw [show (180 : ℝ) * Real.pi / 180 = Real.pi by ring, EuclideanGeometry.angle_comm A B D]; exact EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi D h1.angle₁₂₃_eq_pi

theorem thm_triangle_inequality_points (P : ℂ) (Q : ℂ) (R : ℂ) :
    dist P R ≤ dist P Q + dist Q R :=
  dist_triangle P Q R

theorem mun_angle_addition (A : ℂ) (B : ℂ) (C : ℂ) (M : ℂ) (h1 : LeanBridges.Geometry.Triangle A B C) (h2 : Sbtw ℝ A M B) (h3 : C ≠ M) :
    EuclideanGeometry.angle A C M + EuclideanGeometry.angle M C B = EuclideanGeometry.angle A C B :=
  LeanBridges.Geometry.angle_addition A B C M h1 h2 h3

theorem mun_distance_nonneg (P : ℂ) (Q : ℂ) :
    0 ≤ dist P Q :=
  dist_nonneg

theorem axi_distance_positive (P : ℂ) (Q : ℂ) (h1 : P ≠ Q) :
    0 < dist P Q :=
  dist_pos.mpr h1

theorem mun_distance_zero (P : ℂ) (Q : ℂ) :
    dist P Q = 0 ↔ P = Q :=
  dist_eq_zero

theorem mun_distance_by_coordinates (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) :
    dist (Complex.mk a b) (Complex.mk c d) = Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) :=
  Complex.dist_eq_re_im _ _

theorem mun_collinear_by_coordinates (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) (e : ℝ) (f : ℝ) :
    Collinear ℝ {Complex.mk a b, Complex.mk c d, Complex.mk e f} ↔ (c - a) * (f - b) = (e - a) * (d - b) :=
  LeanBridges.Geometry.collinear_by_coordinates a b c d e f

theorem mun_between_by_coordinates (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) (e : ℝ) (f : ℝ) :
    Sbtw ℝ (Complex.mk a b) (Complex.mk c d) (Complex.mk e f) ↔ (a - c) * (f - d) = (e - c) * (b - d) ∧ (a - c) * (e - c) + (b - d) * (f - d) < 0 :=
  LeanBridges.Geometry.between_by_coordinates a b c d e f

theorem mun_points_apart_by_coordinates (A : ℂ) (B : ℂ) (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) (h5 : A = Complex.mk a b) (h6 : B = Complex.mk c d) :
    A ≠ B ↔ ¬ ((a, b) : ℝ × ℝ) = (c, d) :=
  by rw [h5, h6, ne_eq, Complex.mk.injEq, Prod.mk.injEq]

theorem mun_distance_of_points_by_coordinates (A : ℂ) (B : ℂ) (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) (h5 : A = Complex.mk a b) (h6 : B = Complex.mk c d) :
    dist A B = Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) :=
  by rw [h5, h6]; exact Complex.dist_eq_re_im _ _

theorem mun_between_symmetric (R : ℂ) (S : ℂ) (T : ℂ) (h1 : Sbtw ℝ S R T) :
    Sbtw ℝ T R S :=
  h1.symm

theorem mun_between_apart_1 (R : ℂ) (S : ℂ) (T : ℂ) (h1 : Sbtw ℝ S R T) :
    S ≠ R :=
  h1.ne_left.symm

theorem mun_between_apart_2 (R : ℂ) (S : ℂ) (T : ℂ) (h1 : Sbtw ℝ S R T) :
    T ≠ R :=
  h1.ne_right.symm

theorem mun_between_ends_apart (R : ℂ) (S : ℂ) (T : ℂ) (h1 : Sbtw ℝ S R T) :
    S ≠ T :=
  h1.left_ne_right

theorem mun_between_collinear (R : ℂ) (S : ℂ) (T : ℂ) (h1 : Sbtw ℝ S R T) :
    Collinear ℝ {T, R, S} :=
  h1.symm.wbtw.collinear

theorem mun_triangle_on_side (P : ℂ) (Q : ℂ) (R : ℂ) (S : ℂ) (h1 : LeanBridges.Geometry.Triangle P Q R) (h2 : Sbtw ℝ Q S R) :
    LeanBridges.Geometry.Triangle P Q S :=
  LeanBridges.Geometry.triangle_on_side P Q R S h1 h2

theorem mun_angle_along_segment (P : ℂ) (Q : ℂ) (R : ℂ) (S : ℂ) (h1 : Sbtw ℝ P S Q) (h2 : R ≠ P) (h3 : R ≠ S) (h4 : R ≠ Q) :
    EuclideanGeometry.angle S P R = EuclideanGeometry.angle Q P R :=
  h1.angle_eq_left R

theorem mun_segment_addition (P : ℂ) (Q : ℂ) (S : ℂ) (h1 : Sbtw ℝ P S Q) :
    dist P S + dist S Q = dist P Q :=
  LeanBridges.Geometry.segment_addition P Q S h1

theorem mun_sine_positive (P : ℂ) (Q : ℂ) (R : ℂ) (h1 : LeanBridges.Geometry.Triangle P Q R) :
    0 < Real.sin (EuclideanGeometry.angle P Q R) :=
  EuclideanGeometry.sin_pos_of_not_collinear h1.2.2.2

theorem thm_law_of_sines (P : ℂ) (Q : ℂ) (R : ℂ) (h1 : LeanBridges.Geometry.Triangle P Q R) :
    dist P Q * Real.sin (EuclideanGeometry.angle P Q R) = dist P R * Real.sin (EuclideanGeometry.angle Q R P) :=
  LeanBridges.Geometry.law_of_sines P Q R h1

theorem def_area (P : ℂ) (Q : ℂ) (R : ℂ) :
    1 / 2 * (dist Q R * dist P R) * abs (Real.sin (Complex.arg ((P - R) / (Q - R)))) = 1 / 2 * (dist Q R * dist P R) * abs (Real.sin (Complex.arg ((P - R) / (Q - R)))) :=
  rfl

theorem thm_area_by_sine (P : ℂ) (Q : ℂ) (R : ℂ) (h1 : P ≠ R) (h2 : Q ≠ R) (h3 : Q ≠ P) :
    1 / 2 * (dist Q R * dist P R) * abs (Real.sin (Complex.arg ((P - R) / (Q - R)))) = 1 / 2 * (dist Q R * dist P R) * Real.sin (EuclideanGeometry.angle Q R P) :=
  LeanBridges.Geometry.area_by_sine P Q R h1 h2 h3

theorem mun_area_real (P : ℂ) (Q : ℂ) (R : ℂ) (h1 : P ≠ R) (h2 : Q ≠ R) :
    True :=
  trivial

theorem axi_area_positive (P : ℂ) (Q : ℂ) (R : ℂ) (h1 : LeanBridges.Geometry.Triangle P Q R) :
    0 < 1 / 2 * (dist Q R * dist P R) * abs (Real.sin (Complex.arg ((P - R) / (Q - R)))) :=
  LeanBridges.Geometry.area_positive P Q R h1

theorem thm_heron (P : ℂ) (Q : ℂ) (R : ℂ) (s : ℝ) (h2 : P ≠ R) (h3 : Q ≠ R) (h4 : s = (dist Q R + dist P R + dist P Q) / 2) :
    ((1 / 2 * (dist Q R * dist P R) * abs (Real.sin (Complex.arg ((P - R) / (Q - R)))) : ℝ) : ℂ) = ((s : ℂ) * ((s : ℂ) - (dist Q R : ℂ)) * (((s : ℂ) - (dist P R : ℂ)) * ((s : ℂ) - (dist P Q : ℂ)))) ^ (1 / 2 : ℂ) :=
  LeanBridges.Geometry.heron P Q R s h2 h3 h4

theorem thm_law_of_cosines (P : ℂ) (Q : ℂ) (R : ℂ) (h1 : P ≠ Q) (h2 : R ≠ Q) (h3 : P ≠ R) :
    dist R P ^ 2 = dist P Q ^ 2 + dist Q R ^ 2 - 2 * (dist P Q * dist Q R * Real.cos (EuclideanGeometry.angle P Q R)) :=
  LeanBridges.Geometry.law_of_cosines P Q R h1 h2 h3

theorem mun_angle_equal_by_cosine (P : ℂ) (P' : ℂ) (Q : ℂ) (Q' : ℂ) (R : ℂ) (R' : ℂ) (h1 : P ≠ Q) (h2 : R ≠ Q) (h3 : P' ≠ Q') (h4 : R' ≠ Q') (h5 : Real.cos (EuclideanGeometry.angle P Q R) = Real.cos (EuclideanGeometry.angle P' Q' R')) (h6 : P ≠ R) (h7 : P' ≠ R') :
    EuclideanGeometry.angle P Q R = EuclideanGeometry.angle P' Q' R' :=
  Real.injOn_cos ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩ ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩ h5

theorem mun_angle_order_by_cosine (P : ℂ) (P' : ℂ) (Q : ℂ) (Q' : ℂ) (R : ℂ) (R' : ℂ) (h1 : P ≠ Q) (h2 : R ≠ Q) (h3 : P' ≠ Q') (h4 : R' ≠ Q') (h5 : P ≠ R) (h6 : P' ≠ R') :
    EuclideanGeometry.angle P Q R < EuclideanGeometry.angle P' Q' R' ↔ Real.cos (EuclideanGeometry.angle P' Q' R') < Real.cos (EuclideanGeometry.angle P Q R) :=
  (StrictAntiOn.lt_iff_gt Real.strictAntiOn_cos ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩ ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩).symm

theorem mun_right_angle_by_cosine (P : ℂ) (Q : ℂ) (R : ℂ) (h1 : P ≠ Q) (h2 : R ≠ Q) (h3 : P ≠ R) :
    EuclideanGeometry.angle P Q R = (90 : ℝ) * Real.pi / 180 ↔ Real.cos (EuclideanGeometry.angle P Q R) = 0 :=
  by rw [show (90 : ℝ) * Real.pi / 180 = Real.pi / 2 by ring, ← Real.cos_pi_div_two]; exact Real.injOn_cos.eq_iff ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩ ⟨by positivity, by linarith [Real.pi_pos]⟩ |>.symm

theorem mun_right_angle_triangle (P : ℂ) (Q : ℂ) (R : ℂ) (h1 : P ≠ Q) (h2 : R ≠ Q) (h3 : EuclideanGeometry.angle P Q R = (90 : ℝ) * Real.pi / 180) (h4 : P ≠ R) :
    LeanBridges.Geometry.Triangle P Q R :=
  LeanBridges.Geometry.right_angle_triangle P Q R h1 h2 h3 h4

theorem mun_cosine_right_triangle (P : ℂ) (Q : ℂ) (R : ℂ) (h1 : P ≠ R) (h2 : Q ≠ R) (h3 : EuclideanGeometry.angle P R Q = (90 : ℝ) * Real.pi / 180) (h4 : P ≠ Q) :
    dist Q R = dist Q P * Real.cos (EuclideanGeometry.angle R Q P) :=
  LeanBridges.Geometry.cosine_right_triangle P Q R h1 h2 h3 h4

theorem mun_angle_at_most_straight (P : ℂ) (Q : ℂ) (R : ℂ) (h1 : P ≠ Q) (h2 : R ≠ Q) (h3 : P ≠ R) :
    EuclideanGeometry.angle P Q R ≤ (180 : ℝ) * Real.pi / 180 :=
  (EuclideanGeometry.angle_le_pi P Q R).trans_eq (by ring)

theorem mun_angle_by_cosine (P : ℂ) (Q : ℂ) (R : ℂ) (x : ℝ) (h2 : P ≠ Q) (h3 : R ≠ Q) (h4 : 0 ≤ x) (h5 : x ≤ (180 : ℝ) * Real.pi / 180) (h6 : P ≠ R) :
    EuclideanGeometry.angle P Q R = x ↔ Real.cos (EuclideanGeometry.angle P Q R) = Real.cos x :=
  (Real.injOn_cos.eq_iff ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩ ⟨h4, h5.trans_eq (by ring)⟩).symm

theorem axi_side_angle_side (P : ℂ) (P' : ℂ) (Q : ℂ) (Q' : ℂ) (R : ℂ) (R' : ℂ) (h1 : LeanBridges.Geometry.Triangle P Q R) (h2 : LeanBridges.Geometry.Triangle P' Q' R') (h3 : dist P Q = dist P' Q') (h4 : EuclideanGeometry.angle P Q R = EuclideanGeometry.angle P' Q' R') (h5 : dist Q R = dist Q' R') :
    dist P Q = dist P' Q' ∧ dist Q R = dist Q' R' ∧ dist R P = dist R' P' ∧ EuclideanGeometry.angle P Q R = EuclideanGeometry.angle P' Q' R' ∧ EuclideanGeometry.angle Q R P = EuclideanGeometry.angle Q' R' P' ∧ EuclideanGeometry.angle R P Q = EuclideanGeometry.angle R' P' Q' :=
  LeanBridges.Geometry.side_angle_side P P' Q Q' R R' h1 h2 h3 h4 h5

theorem axi_line_uniqueness (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (h1 : A ≠ B) (h2 : C ≠ D) (h3 : A ∈ LeanBridges.Geometry.line C D) (h4 : B ∈ LeanBridges.Geometry.line C D) :
    LeanBridges.Geometry.line A B = LeanBridges.Geometry.line C D :=
  LeanBridges.Geometry.line_uniqueness A B C D h1 h2 h3 h4

theorem axi_three_points :
    ∃ P ∈ (Set.univ : Set ℂ), ∃ Q ∈ (Set.univ : Set ℂ), ∃ R ∈ (Set.univ : Set ℂ), LeanBridges.Geometry.Triangle P Q R :=
  LeanBridges.Geometry.three_points

theorem axi_angle_measure_1 (P : ℂ) (Q : ℂ) (R : ℂ) (h1 : LeanBridges.Geometry.Triangle P Q R) :
    (0 : ℝ) * Real.pi / 180 < EuclideanGeometry.angle P Q R :=
  by linarith [EuclideanGeometry.angle_pos_of_not_collinear h1.2.2.2]

theorem axi_angle_measure_2 (P : ℂ) (Q : ℂ) (R : ℂ) (h1 : LeanBridges.Geometry.Triangle P Q R) :
    EuclideanGeometry.angle P Q R < (180 : ℝ) * Real.pi / 180 :=
  by linarith [EuclideanGeometry.angle_lt_pi_of_not_collinear h1.2.2.2]

theorem axi_ruler (A : ℂ) (B : ℂ) (h1 : A ≠ B) :
    ∃ f : ℂ → ℝ, Set.MapsTo f (LeanBridges.Geometry.line A B) (Set.univ : Set ℝ) ∧ ((Set.MapsTo f (LeanBridges.Geometry.line A B) (Set.univ : Set ℝ) ∧ Set.InjOn f (LeanBridges.Geometry.line A B) ∧ Set.SurjOn f (LeanBridges.Geometry.line A B) (Set.univ : Set ℝ)) ∧ (∀ P ∈ LeanBridges.Geometry.line A B, ∀ Q ∈ LeanBridges.Geometry.line A B, dist P Q = abs (f P - f Q))) :=
  LeanBridges.Geometry.ruler A B h1

theorem axi_ruler_placement (A : ℂ) (B : ℂ) (h1 : A ≠ B) :
    ∃ f : ℂ → ℝ, Set.MapsTo f (LeanBridges.Geometry.line A B) (Set.univ : Set ℝ) ∧ ((((Set.MapsTo f (LeanBridges.Geometry.line A B) (Set.univ : Set ℝ) ∧ Set.InjOn f (LeanBridges.Geometry.line A B) ∧ Set.SurjOn f (LeanBridges.Geometry.line A B) (Set.univ : Set ℝ)) ∧ f A = 0) ∧ 0 < f B) ∧ (∀ P ∈ LeanBridges.Geometry.line A B, ∀ Q ∈ LeanBridges.Geometry.line A B, dist P Q = abs (f P - f Q))) :=
  LeanBridges.Geometry.ruler_placement A B h1

theorem axi_parallel_uniqueness (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (P : ℂ) (h1 : A ≠ B) (h2 : ¬ P ∈ LeanBridges.Geometry.line A B) (h3 : P ≠ C) (h4 : P ≠ D) (h5 : Complex.im ((C - P) / (B - A)) = 0) (h6 : Complex.im ((D - P) / (B - A)) = 0) :
    LeanBridges.Geometry.line P C = LeanBridges.Geometry.line P D :=
  LeanBridges.Geometry.parallel_uniqueness A B C D P h1 h2 h3 h4 h5 h6

theorem axi_plane_separation (A : ℂ) (B : ℂ) (P : ℂ) (Q : ℂ) (h1 : A ≠ B) (h2 : ¬ P ∈ LeanBridges.Geometry.line A B) (h3 : ¬ Q ∈ LeanBridges.Geometry.line A B) :
    0 < Complex.im ((P - A) / (B - A)) * Complex.im ((Q - A) / (B - A)) ∨ Complex.im ((P - A) / (B - A)) * Complex.im ((Q - A) / (B - A)) < 0 :=
  LeanBridges.Geometry.plane_separation A B P Q h1 h2 h3

theorem axi_plane_separation_convex (A : ℂ) (B : ℂ) (P : ℂ) (Q : ℂ) (X : ℂ) (h1 : A ≠ B) (h2 : 0 < Complex.im ((P - A) / (B - A)) * Complex.im ((Q - A) / (B - A))) (h3 : Sbtw ℝ P X Q) :
    0 < Complex.im ((X - A) / (B - A)) * Complex.im ((P - A) / (B - A)) :=
  LeanBridges.Geometry.plane_separation_convex A B P Q X h1 h2 h3

theorem axi_plane_separation_crossing (A : ℂ) (B : ℂ) (P : ℂ) (Q : ℂ) (h1 : A ≠ B) (h2 : Complex.im ((P - A) / (B - A)) * Complex.im ((Q - A) / (B - A)) < 0) :
    ∃ X ∈ (Set.univ : Set ℂ), X ∈ LeanBridges.Geometry.line A B ∧ Sbtw ℝ P X Q :=
  LeanBridges.Geometry.plane_separation_crossing A B P Q h1 h2

theorem axi_angle_construction (A : ℂ) (B : ℂ) (C : ℂ) (x : ℝ) (h2 : LeanBridges.Geometry.Triangle A B C) (h3 : (0 : ℝ) * Real.pi / 180 < x) (h4 : x < (180 : ℝ) * Real.pi / 180) :
    ∃ D ∈ (Set.univ : Set ℂ), 0 < Complex.im ((D - A) / (B - A)) * Complex.im ((C - A) / (B - A)) ∧ EuclideanGeometry.angle B A D = x :=
  LeanBridges.Geometry.angle_construction A B C x h2 h3 h4

theorem axi_angle_construction_unique (E : ℂ) (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (h1 : LeanBridges.Geometry.Triangle A B C) (h2 : 0 < Complex.im ((D - A) / (B - A)) * Complex.im ((C - A) / (B - A))) (h3 : 0 < Complex.im ((E - A) / (B - A)) * Complex.im ((C - A) / (B - A))) (h4 : EuclideanGeometry.angle B A D = EuclideanGeometry.angle B A E) :
    E ∈ LeanBridges.Geometry.ray A D :=
  LeanBridges.Geometry.angle_construction_unique E A B C D h1 h2 h3 h4

theorem axi_angle_addition_inside (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (h1 : LeanBridges.Geometry.Triangle A B C) (h2 : 0 < Complex.im ((D - A) / (B - A)) * Complex.im ((C - A) / (B - A))) (h3 : 0 < Complex.im ((D - A) / (C - A)) * Complex.im ((B - A) / (C - A))) :
    EuclideanGeometry.angle B A D + EuclideanGeometry.angle D A C = EuclideanGeometry.angle B A C :=
  LeanBridges.Geometry.angle_addition_inside A B C D h1 h2 h3

theorem axi_area_congruent (P : ℂ) (P' : ℂ) (Q : ℂ) (Q' : ℂ) (R : ℂ) (R' : ℂ) (h1 : LeanBridges.Geometry.Triangle P Q R) (h2 : LeanBridges.Geometry.Triangle P' Q' R') (h3 : dist P Q = dist P' Q' ∧ dist Q R = dist Q' R' ∧ dist R P = dist R' P' ∧ EuclideanGeometry.angle P Q R = EuclideanGeometry.angle P' Q' R' ∧ EuclideanGeometry.angle Q R P = EuclideanGeometry.angle Q' R' P' ∧ EuclideanGeometry.angle R P Q = EuclideanGeometry.angle R' P' Q') :
    1 / 2 * (dist Q R * dist P R) * abs (Real.sin (Complex.arg ((P - R) / (Q - R)))) = 1 / 2 * (dist Q' R' * dist P' R') * abs (Real.sin (Complex.arg ((P' - R') / (Q' - R')))) :=
  LeanBridges.Geometry.area_congruent P P' Q Q' R R' h1 h2 h3

theorem axi_area_base_height (H : ℂ) (P : ℂ) (Q : ℂ) (R : ℂ) (h1 : LeanBridges.Geometry.Triangle P Q R) (h2 : H ∈ LeanBridges.Geometry.line Q R) (h3 : P ≠ H ∧ Q ≠ R ∧ Complex.re ((R - Q) / (H - P)) = 0) :
    1 / 2 * (dist Q R * dist P R) * abs (Real.sin (Complex.arg ((P - R) / (Q - R)))) = 1 / 2 * dist Q R * dist P H :=
  LeanBridges.Geometry.area_base_height H P Q R h1 h2 h3

theorem axi_area_addition (D : ℂ) (P : ℂ) (Q : ℂ) (R : ℂ) (h1 : LeanBridges.Geometry.Triangle P Q R) (h2 : Sbtw ℝ Q D R) :
    1 / 2 * (dist Q R * dist P R) * abs (Real.sin (Complex.arg ((P - R) / (Q - R)))) = 1 / 2 * (dist Q D * dist P D) * abs (Real.sin (Complex.arg ((P - D) / (Q - D)))) + 1 / 2 * (dist D R * dist P R) * abs (Real.sin (Complex.arg ((P - R) / (D - R)))) :=
  LeanBridges.Geometry.area_addition D P Q R h1 h2

theorem mun_midpoint_exists (A : ℂ) (B : ℂ) (h1 : A ≠ B) :
    ∃ M ∈ (Set.univ : Set ℂ), Sbtw ℝ A M B ∧ dist A M = dist M B :=
  ⟨midpoint ℝ A B, Set.mem_univ _, sbtw_midpoint_of_ne ℝ h1, by rw [dist_left_midpoint_eq_dist_right_midpoint, dist_comm]⟩

theorem mun_segment_extension (A : ℂ) (B : ℂ) (r : ℝ) (h2 : A ≠ B) (h3 : 0 < r) :
    ∃ X ∈ (Set.univ : Set ℂ), Sbtw ℝ A B X ∧ dist B X = r :=
  LeanBridges.Geometry.segment_extension A B r h2 h3

theorem mun_segment_point (A : ℂ) (B : ℂ) (r : ℝ) (h2 : 0 < r) (h3 : r < dist A B) :
    ∃ X ∈ (Set.univ : Set ℂ), Sbtw ℝ A X B ∧ dist A X = r :=
  LeanBridges.Geometry.segment_point A B r h2 h3

theorem mun_triangle_off_line (P : ℂ) (Q : ℂ) (R : ℂ) (h1 : Q ≠ R) (h2 : ¬ P ∈ LeanBridges.Geometry.line Q R) :
    LeanBridges.Geometry.Triangle P Q R :=
  LeanBridges.Geometry.triangle_off_line P Q R h1 h2

theorem mun_ray_on_line (P : ℂ) (A : ℂ) (B : ℂ) (h1 : P ∈ LeanBridges.Geometry.ray A B) :
    P ∈ LeanBridges.Geometry.line A B :=
  ⟨h1.1, h1.2.1⟩

theorem mun_same_not_opposite (A : ℂ) (B : ℂ) (P : ℂ) (Q : ℂ) (h1 : 0 < Complex.im ((P - A) / (B - A)) * Complex.im ((Q - A) / (B - A))) :
    ¬ Complex.im ((P - A) / (B - A)) * Complex.im ((Q - A) / (B - A)) < 0 :=
  not_lt.mpr h1.le

theorem mun_parallel_turned (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (h1 : A ≠ B) (h2 : Complex.im ((B - A) / (D - C)) = 0) :
    Complex.im ((D - C) / (B - A)) = 0 :=
  by rw [← inv_div, Complex.inv_im, h2, neg_zero, zero_div]

theorem mun_perpendicular_turned (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (h1 : A ≠ B ∧ C ≠ D ∧ Complex.re ((D - C) / (B - A)) = 0) :
    B ≠ A ∧ C ≠ D ∧ Complex.re ((D - C) / (A - B)) = 0 :=
  ⟨h1.1.symm, h1.2.1, by rw [← neg_sub B A, div_neg, Complex.neg_re, h1.2.2, neg_zero]⟩

theorem mun_perpendicular_along (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (E : ℂ) (F : ℂ) (h1 : A ≠ B ∧ C ≠ D ∧ Complex.re ((D - C) / (B - A)) = 0) (h2 : E ∈ LeanBridges.Geometry.line C D) (h3 : F ∈ LeanBridges.Geometry.line C D) (h4 : E ≠ F) :
    A ≠ B ∧ E ≠ F ∧ Complex.re ((F - E) / (B - A)) = 0 :=
  LeanBridges.Geometry.perpendicular_along A B C D E F h1 h2 h3 h4

theorem mun_area_rotated (P : ℂ) (Q : ℂ) (R : ℂ) (h1 : LeanBridges.Geometry.Triangle P Q R) :
    1 / 2 * (dist Q R * dist P R) * abs (Real.sin (Complex.arg ((P - R) / (Q - R)))) = 1 / 2 * (dist R P * dist Q P) * abs (Real.sin (Complex.arg ((Q - P) / (R - P)))) :=
  LeanBridges.Geometry.area_rotated P Q R h1

theorem mun_same_side_turned (A : ℂ) (B : ℂ) (P : ℂ) (Q : ℂ) (h1 : 0 < Complex.im ((P - A) / (B - A)) * Complex.im ((Q - A) / (B - A))) :
    0 < Complex.im ((Q - A) / (B - A)) * Complex.im ((P - A) / (B - A)) :=
  by rwa [mul_comm]

theorem mun_opposite_sides_turned (A : ℂ) (B : ℂ) (P : ℂ) (Q : ℂ) (h1 : Complex.im ((P - A) / (B - A)) * Complex.im ((Q - A) / (B - A)) < 0) :
    Complex.im ((Q - A) / (B - A)) * Complex.im ((P - A) / (B - A)) < 0 :=
  by rwa [mul_comm]

theorem mun_same_side_same (A : ℂ) (B : ℂ) (P : ℂ) (Q : ℂ) (R : ℂ) (h1 : 0 < Complex.im ((P - A) / (B - A)) * Complex.im ((Q - A) / (B - A))) (h2 : 0 < Complex.im ((Q - A) / (B - A)) * Complex.im ((R - A) / (B - A))) :
    0 < Complex.im ((P - A) / (B - A)) * Complex.im ((R - A) / (B - A)) :=
  by nlinarith [mul_pos h1 h2, sq_nonneg (Complex.im ((Q - A) / (B - A)))]

theorem mun_opposite_opposite_same (A : ℂ) (B : ℂ) (P : ℂ) (Q : ℂ) (R : ℂ) (h1 : Complex.im ((P - A) / (B - A)) * Complex.im ((Q - A) / (B - A)) < 0) (h2 : Complex.im ((Q - A) / (B - A)) * Complex.im ((R - A) / (B - A)) < 0) :
    0 < Complex.im ((P - A) / (B - A)) * Complex.im ((R - A) / (B - A)) :=
  by nlinarith [mul_pos_of_neg_of_neg h1 h2, sq_nonneg (Complex.im ((Q - A) / (B - A)))]

theorem mun_same_opposite_opposite (A : ℂ) (B : ℂ) (P : ℂ) (Q : ℂ) (R : ℂ) (h1 : 0 < Complex.im ((P - A) / (B - A)) * Complex.im ((Q - A) / (B - A))) (h2 : Complex.im ((Q - A) / (B - A)) * Complex.im ((R - A) / (B - A)) < 0) :
    Complex.im ((P - A) / (B - A)) * Complex.im ((R - A) / (B - A)) < 0 :=
  by nlinarith [mul_neg_of_pos_of_neg h1 h2, sq_nonneg (Complex.im ((Q - A) / (B - A)))]

theorem mun_same_side_of_line (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (P : ℂ) (Q : ℂ) (h1 : A ≠ B) (h2 : C ≠ D) (h3 : C ∈ LeanBridges.Geometry.line A B) (h4 : D ∈ LeanBridges.Geometry.line A B) (h5 : 0 < Complex.im ((P - A) / (B - A)) * Complex.im ((Q - A) / (B - A))) :
    0 < Complex.im ((P - C) / (D - C)) * Complex.im ((Q - C) / (D - C)) :=
  LeanBridges.Geometry.same_side_of_line A B C D P Q h1 h2 h3 h4 h5

theorem mun_opposite_sides_of_line (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (P : ℂ) (Q : ℂ) (h1 : A ≠ B) (h2 : C ≠ D) (h3 : C ∈ LeanBridges.Geometry.line A B) (h4 : D ∈ LeanBridges.Geometry.line A B) (h5 : Complex.im ((P - A) / (B - A)) * Complex.im ((Q - A) / (B - A)) < 0) :
    Complex.im ((P - C) / (D - C)) * Complex.im ((Q - C) / (D - C)) < 0 :=
  LeanBridges.Geometry.opposite_sides_of_line A B C D P Q h1 h2 h3 h4 h5

theorem mun_segment_off_line (A : ℂ) (B : ℂ) (P : ℂ) (Q : ℂ) (X : ℂ) (h1 : A ≠ B) (h2 : Q ∈ LeanBridges.Geometry.line A B) (h3 : ¬ P ∈ LeanBridges.Geometry.line A B) (h4 : Sbtw ℝ P X Q) :
    0 < Complex.im ((X - A) / (B - A)) * Complex.im ((P - A) / (B - A)) :=
  LeanBridges.Geometry.segment_off_line A B P Q X h1 h2 h3 h4

theorem mun_segment_across_line (A : ℂ) (B : ℂ) (M : ℂ) (P : ℂ) (Q : ℂ) (h1 : A ≠ B) (h2 : M ∈ LeanBridges.Geometry.line A B) (h3 : ¬ P ∈ LeanBridges.Geometry.line A B) (h4 : Sbtw ℝ P M Q) :
    Complex.im ((P - A) / (B - A)) * Complex.im ((Q - A) / (B - A)) < 0 :=
  LeanBridges.Geometry.segment_across_line A B M P Q h1 h2 h3 h4

theorem mun_segment_beyond_off_line (A : ℂ) (B : ℂ) (P : ℂ) (Q : ℂ) (X : ℂ) (h1 : A ≠ B) (h2 : Q ∈ LeanBridges.Geometry.line A B) (h3 : ¬ X ∈ LeanBridges.Geometry.line A B) (h4 : Sbtw ℝ P X Q) :
    0 < Complex.im ((P - A) / (B - A)) * Complex.im ((X - A) / (B - A)) :=
  LeanBridges.Geometry.segment_beyond_off_line A B P Q X h1 h2 h3 h4

theorem mun_same_side_off_line_1 (A : ℂ) (B : ℂ) (P : ℂ) (Q : ℂ) (h1 : 0 < Complex.im ((P - A) / (B - A)) * Complex.im ((Q - A) / (B - A))) :
    A ≠ B :=
  by rintro rfl; simp at h1

theorem mun_same_side_off_line_2 (A : ℂ) (B : ℂ) (P : ℂ) (Q : ℂ) (h1 : 0 < Complex.im ((P - A) / (B - A)) * Complex.im ((Q - A) / (B - A))) :
    ¬ P ∈ LeanBridges.Geometry.line A B :=
  fun h => by rw [h.2, zero_mul] at h1; exact lt_irrefl 0 h1

theorem mun_same_side_off_line_3 (A : ℂ) (B : ℂ) (P : ℂ) (Q : ℂ) (h1 : 0 < Complex.im ((P - A) / (B - A)) * Complex.im ((Q - A) / (B - A))) :
    ¬ Q ∈ LeanBridges.Geometry.line A B :=
  fun h => by rw [h.2, mul_zero] at h1; exact lt_irrefl 0 h1

theorem mun_opposite_sides_off_line_1 (A : ℂ) (B : ℂ) (P : ℂ) (Q : ℂ) (h1 : Complex.im ((P - A) / (B - A)) * Complex.im ((Q - A) / (B - A)) < 0) :
    A ≠ B :=
  by rintro rfl; simp at h1

theorem mun_opposite_sides_off_line_2 (A : ℂ) (B : ℂ) (P : ℂ) (Q : ℂ) (h1 : Complex.im ((P - A) / (B - A)) * Complex.im ((Q - A) / (B - A)) < 0) :
    ¬ P ∈ LeanBridges.Geometry.line A B :=
  fun h => by rw [h.2, zero_mul] at h1; exact lt_irrefl 0 h1

theorem mun_opposite_sides_off_line_3 (A : ℂ) (B : ℂ) (P : ℂ) (Q : ℂ) (h1 : Complex.im ((P - A) / (B - A)) * Complex.im ((Q - A) / (B - A)) < 0) :
    ¬ Q ∈ LeanBridges.Geometry.line A B :=
  fun h => by rw [h.2, mul_zero] at h1; exact lt_irrefl 0 h1

theorem mun_on_line_ends_1 (A : ℂ) (B : ℂ) (h1 : A ≠ B) :
    A ∈ LeanBridges.Geometry.line A B :=
  ⟨h1, by simp⟩

theorem mun_on_line_ends_2 (A : ℂ) (B : ℂ) (h1 : A ≠ B) :
    B ∈ LeanBridges.Geometry.line A B :=
  ⟨h1, by simp [div_self (sub_ne_zero.mpr h1.symm)]⟩

theorem mun_triangle_not_on_line (P : ℂ) (Q : ℂ) (R : ℂ) (h1 : LeanBridges.Geometry.Triangle P Q R) :
    ¬ P ∈ LeanBridges.Geometry.line Q R :=
  fun h => h1.2.2.2 ((LeanBridges.Geometry.collinear_rot_231 P Q R).mpr ((LeanBridges.Geometry.mem_line_iff_collinear Q R P h1.2.1).mp h))

theorem mun_triangle_extension (P : ℂ) (Q : ℂ) (R : ℂ) (S : ℂ) (h1 : LeanBridges.Geometry.Triangle P Q R) (h2 : Sbtw ℝ R Q S) :
    LeanBridges.Geometry.Triangle P Q S :=
  LeanBridges.Geometry.triangle_extension P Q R S h1 h2

theorem mun_off_line_apart_1 (A : ℂ) (B : ℂ) (P : ℂ) (h1 : A ≠ B) (h2 : ¬ P ∈ LeanBridges.Geometry.line A B) :
    P ≠ A :=
  fun h => h2 (by rw [h]; exact ⟨h1, by simp⟩)

theorem mun_off_line_apart_2 (A : ℂ) (B : ℂ) (P : ℂ) (h1 : A ≠ B) (h2 : ¬ P ∈ LeanBridges.Geometry.line A B) :
    P ≠ B :=
  fun h => h2 (by rw [h]; exact ⟨h1, by simp [div_self (sub_ne_zero.mpr h1.symm)]⟩)

theorem mun_on_off_apart (A : ℂ) (B : ℂ) (X : ℂ) (Y : ℂ) (h1 : X ∈ LeanBridges.Geometry.line A B) (h2 : ¬ Y ∈ LeanBridges.Geometry.line A B) :
    X ≠ Y :=
  fun h => h2 (h ▸ h1)

theorem mun_off_line_through (P : ℂ) (R : ℂ) (S : ℂ) (X : ℂ) (h1 : ¬ S ∈ LeanBridges.Geometry.line R P) (h2 : X ∈ LeanBridges.Geometry.line R S) (h3 : X ≠ R) :
    ¬ X ∈ LeanBridges.Geometry.line R P :=
  LeanBridges.Geometry.off_line_through P R S X h1 h2 h3

theorem mun_line_crossing_between (P : ℂ) (R : ℂ) (S : ℂ) (X : ℂ) (h1 : X ∈ LeanBridges.Geometry.line R S) (h2 : Complex.im ((S - R) / (P - R)) * Complex.im ((X - R) / (P - R)) < 0) :
    Sbtw ℝ S R X :=
  LeanBridges.Geometry.line_crossing_between P R S X h1 h2

theorem mun_angle_same_ray (P : ℂ) (Q : ℂ) (R : ℂ) (X : ℂ) (h1 : X ∈ LeanBridges.Geometry.line P Q) (h2 : 0 < Complex.im ((X - P) / (R - P)) * Complex.im ((Q - P) / (R - P))) :
    EuclideanGeometry.angle R P X = EuclideanGeometry.angle R P Q :=
  LeanBridges.Geometry.angle_same_ray P Q R X h1 h2

theorem mun_ray_side_transfer (P : ℂ) (Q : ℂ) (R : ℂ) (S : ℂ) (X : ℂ) (h1 : X ∈ LeanBridges.Geometry.line R P) (h2 : 0 < Complex.im ((X - R) / (S - R)) * Complex.im ((P - R) / (S - R))) (h3 : R ≠ Q) (h4 : ¬ P ∈ LeanBridges.Geometry.line R Q) :
    0 < Complex.im ((X - R) / (Q - R)) * Complex.im ((P - R) / (Q - R)) :=
  LeanBridges.Geometry.ray_side_transfer P Q R S X h1 h2 h3 h4

theorem mun_parallel_along (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (E : ℂ) (h1 : Complex.im ((B - A) / (D - C)) = 0) (h2 : A ≠ B) (h3 : E ∈ LeanBridges.Geometry.line A B) (h4 : E ≠ A) :
    Complex.im ((E - A) / (C - D)) = 0 :=
  LeanBridges.Geometry.parallel_along A B C D E h1 h2 h3 h4

theorem mun_off_line_swap (P : ℂ) (Q : ℂ) (R : ℂ) (h1 : R ≠ P) (h2 : ¬ Q ∈ LeanBridges.Geometry.line R P) :
    ¬ P ∈ LeanBridges.Geometry.line R Q :=
  fun h => h2 ((LeanBridges.Geometry.mem_line_iff_collinear R P Q h1).mpr ((LeanBridges.Geometry.collinear_swap_23 R Q P).mp ((LeanBridges.Geometry.mem_line_iff_collinear R Q P h.1).mp h)))

end Parley.Items.Stdlib.Geometry
