module

public import Lean.Parser.Command
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.Complex.Angle
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle
public import Mathlib.Geometry.Euclidean.Triangle
public import Mathlib.Analysis.Normed.Affine.Convex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Geometry.Euclidean.Congruence

/-!
# Geometry

A point is a complex number, as set.mm's plane is, and the page's notations
for points are Mathlib's terms (`dist`, `EuclideanGeometry.angle`, `Sbtw`,
`Collinear`) or the formulas the page defines them by. The line through two
points and the ray from one through another are sets of points the page
defines, and Mathlib has none that agrees on every input: its line through
a point and itself is that point, and the page's is the plane.
-/

public section

namespace LeanBridges.Geometry

/-- `P, Q, R form a triangle`: the three are apart and not on one line, as
`def:stdlib/geometry/triangle` says. It stands as one predicate, so that the
page's reading of it in any order of the three points is two swaps of it
(`triangle_swap_12`, `triangle_swap_23`). -/
abbrev Triangle (P Q R : ℂ) : Prop :=
  P ≠ Q ∧ Q ≠ R ∧ P ≠ R ∧ ¬ Collinear ℝ {P, Q, R}

theorem triangle_swap_12 (P Q R : ℂ) : Triangle P Q R ↔ Triangle Q P R := by
  unfold Triangle
  rw [Set.insert_comm P Q {R}]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1.symm, h3, h2, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1.symm, h3, h2, h4⟩

theorem triangle_swap_23 (P Q R : ℂ) : Triangle P Q R ↔ Triangle P R Q := by
  unfold Triangle
  rw [Set.pair_comm Q R]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h3, h2.symm, h1, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h3, h2.symm, h1, h4⟩

theorem triangle_swap_13 (P Q R : ℂ) : Triangle P Q R ↔ Triangle R Q P :=
  (triangle_swap_12 P Q R).trans
    ((triangle_swap_23 Q P R).trans (triangle_swap_12 Q R P))

theorem triangle_rot_231 (P Q R : ℂ) : Triangle P Q R ↔ Triangle Q R P :=
  (triangle_swap_12 P Q R).trans (triangle_swap_23 Q P R)

theorem triangle_rot_312 (P Q R : ℂ) : Triangle P Q R ↔ Triangle R P Q :=
  (triangle_swap_23 P Q R).trans (triangle_swap_12 P R Q)

/-- The three points on one line, in each order of them: the page reads
`P, Q, R are collinear` in any order, and Lean's set of three is ordered.
Each order is one rewrite of the others, so that simp reaches one form. -/
theorem collinear_swap_12 (P Q R : ℂ) :
    Collinear ℝ ({P, Q, R} : Set ℂ) ↔ Collinear ℝ ({Q, P, R} : Set ℂ) := by
  rw [Set.insert_comm P Q {R}]

theorem collinear_swap_23 (P Q R : ℂ) :
    Collinear ℝ ({P, Q, R} : Set ℂ) ↔ Collinear ℝ ({P, R, Q} : Set ℂ) := by
  rw [Set.pair_comm Q R]

theorem collinear_swap_13 (P Q R : ℂ) :
    Collinear ℝ ({P, Q, R} : Set ℂ) ↔ Collinear ℝ ({R, Q, P} : Set ℂ) :=
  (collinear_swap_12 P Q R).trans
    ((collinear_swap_23 Q P R).trans (collinear_swap_12 Q R P))

theorem collinear_rot_231 (P Q R : ℂ) :
    Collinear ℝ ({P, Q, R} : Set ℂ) ↔ Collinear ℝ ({Q, R, P} : Set ℂ) :=
  (collinear_swap_12 P Q R).trans (collinear_swap_23 Q P R)

theorem collinear_rot_312 (P Q R : ℂ) :
    Collinear ℝ ({P, Q, R} : Set ℂ) ↔ Collinear ℝ ({R, P, Q} : Set ℂ) :=
  (collinear_swap_23 P Q R).trans (collinear_swap_12 P R Q)

/-- `M is the midpoint of AB` in either order of the two ends, as the page
reads it: the betweenness turned and each distance's two points exchanged. -/
theorem midpoint_comm (M A B : ℂ) :
    (Sbtw ℝ A M B ∧ dist A M = dist M B) ↔ (Sbtw ℝ B M A ∧ dist B M = dist M A) := by
  rw [sbtw_comm, dist_comm A M, dist_comm M B, dist_comm B M, dist_comm M A]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2.symm⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2.symm⟩

/-- The line through `A` and `B`, apart: the points `P` with `(P − A)/(B − A)`
real. Of one point twice it is nothing, as it is no line, and the page says
`A ≠ B` wherever it writes one. -/
@[expose] def line (A B : ℂ) : Set ℂ :=
  {P | A ≠ B ∧ Complex.im ((P - A) / (B - A)) = 0}

/-- The ray from `A` through `B`, apart: the points `P` with `(P − A)/(B − A)`
a real number at least 0. Of one point twice it is nothing, as for `line`. -/
@[expose] def ray (A B : ℂ) : Set ℂ :=
  {P | A ≠ B ∧ Complex.im ((P - A) / (B - A)) = 0 ∧ 0 ≤ Complex.re ((P - A) / (B - A))}

/-- A point is on the line through two points apart exactly when the three are
collinear (`def:stdlib/geometry/on-line`). -/
theorem mem_line_iff_collinear (A B P : ℂ) (h : A ≠ B) :
    P ∈ line A B ↔ Collinear ℝ ({A, B, P} : Set ℂ) := by
  have hBA : B - A ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  simp only [line, Set.mem_ofPred_eq, h, true_and, ne_eq, not_false_eq_true]
  rw [collinear_iff_of_mem (p₀ := A) (by simp)]
  constructor
  · intro him
    refine ⟨B - A, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · refine ⟨((p - A) / (B - A)).re, ?_⟩
      have : (p - A) / (B - A) = (((p - A) / (B - A)).re : ℂ) := by
        apply Complex.ext <;> simp [him]
      simp only [vadd_eq_add, Complex.real_smul]
      rw [← this]; field_simp; ring
  · rintro ⟨v, hv⟩
    obtain ⟨r, hr⟩ := hv P (by simp)
    obtain ⟨s, hs⟩ := hv B (by simp)
    simp only [vadd_eq_add, Complex.real_smul] at hr hs
    have hs0 : (s : ℂ) ≠ 0 := by
      intro h0
      rw [h0] at hs
      simp only [zero_mul, zero_add] at hs
      exact h hs.symm
    have hv' : v = (B - A) / s := by field_simp; linear_combination (-1 : ℂ) * hs
    have : (P - A) / (B - A) = (r : ℂ) / s := by
      rw [show P - A = r * v by linear_combination hr, hv']; field_simp
    rw [this]; simp [Complex.div_ofReal_im]

/-- The angle at `Q` is the size of the signed angle from `QP` to `QR`. -/
theorem angle_eq_abs_signed_angle (P Q R : ℂ) (h1 : P ≠ Q) (h2 : R ≠ Q) :
    EuclideanGeometry.angle P Q R = |Complex.arg ((R - Q) / (P - Q))| := by
  rw [EuclideanGeometry.angle_comm]
  unfold EuclideanGeometry.angle
  rw [vsub_eq_sub, vsub_eq_sub]
  exact Complex.angle_eq_abs_arg (sub_ne_zero.mpr h2) (sub_ne_zero.mpr h1)

/-- `mun:stdlib/geometry/signed-angle-size`: the angle is the signed angle's size. -/
theorem signed_angle_size (P Q R : ℂ) (h1 : P ≠ Q) (h2 : R ≠ Q) (_h3 : P ≠ R) :
    abs (Complex.arg ((R - Q) / (P - Q))) = EuclideanGeometry.angle P Q R :=
  (angle_eq_abs_signed_angle P Q R h1 h2).symm

/-- `thm:stdlib/geometry/signed-angle-sum`: the signed angles of a triangle turned
the same way round it add to `π` or `−π`. Their quotients multiply to `−1`, so the
sum is `π` up to whole turns, and it cannot be `3π`: two of them `π` would put each
of two points between the other two. -/
theorem signed_angle_sum (P Q R : ℂ) (h1 : P ≠ Q) (h2 : Q ≠ R) (h3 : P ≠ R) :
    Complex.arg ((P - Q) / (R - Q)) + Complex.arg ((Q - R) / (P - R)) +
      Complex.arg ((R - P) / (Q - P)) ∈ ({-Real.pi, Real.pi} : Set ℝ) := by
  have hPQ : P - Q ≠ 0 := sub_ne_zero.mpr h1
  have hQR : Q - R ≠ 0 := sub_ne_zero.mpr h2
  have hPR : P - R ≠ 0 := sub_ne_zero.mpr h3
  have hRQ : R - Q ≠ 0 := sub_ne_zero.mpr h2.symm
  have hRP : R - P ≠ 0 := sub_ne_zero.mpr h3.symm
  have hQP : Q - P ≠ 0 := sub_ne_zero.mpr h1.symm
  have a0 : (P - Q) / (R - Q) ≠ 0 := div_ne_zero hPQ hRQ
  have b0 : (Q - R) / (P - R) ≠ 0 := div_ne_zero hQR hPR
  have c0 : (R - P) / (Q - P) ≠ 0 := div_ne_zero hRP hQP
  have hprod : (P - Q) / (R - Q) * ((Q - R) / (P - R)) * ((R - P) / (Q - P)) = -1 := by
    field_simp; ring
  have hab : (Q - R) / (P - R) * (1 - (P - Q) / (R - Q)) = 1 := by
    field_simp; ring
  have hang : ((Complex.arg ((P - Q) / (R - Q)) + Complex.arg ((Q - R) / (P - R))
      + Complex.arg ((R - P) / (Q - P)) : ℝ) : Real.Angle) = (Real.pi : Real.Angle) := by
    rw [Real.Angle.coe_add, Real.Angle.coe_add, ← Complex.arg_mul_coe_angle a0 b0,
      ← Complex.arg_mul_coe_angle (mul_ne_zero a0 b0) c0, hprod, Complex.arg_neg_one]
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hang
  have la := Complex.neg_pi_lt_arg ((P - Q) / (R - Q))
  have ua := Complex.arg_le_pi ((P - Q) / (R - Q))
  have lb := Complex.neg_pi_lt_arg ((Q - R) / (P - R))
  have ub := Complex.arg_le_pi ((Q - R) / (P - R))
  have lc := Complex.neg_pi_lt_arg ((R - P) / (Q - P))
  have uc := Complex.arg_le_pi ((R - P) / (Q - P))
  have hpi := Real.pi_pos
  have kle : k ≤ 1 := by
    by_contra h
    have : (2 : ℝ) ≤ k := by exact_mod_cast (by omega : 2 ≤ k)
    nlinarith
  have kge : -1 ≤ k := by
    by_contra h
    have : (k : ℝ) ≤ -2 := by exact_mod_cast (by omega : k ≤ -2)
    nlinarith
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  interval_cases k
  · left; push_cast at hk; linarith
  · right; push_cast at hk; linarith
  · exfalso
    push_cast at hk
    have ha : Complex.arg ((P - Q) / (R - Q)) = Real.pi := by linarith
    have hb : Complex.arg ((Q - R) / (P - R)) = Real.pi := by linarith
    rw [Complex.arg_eq_pi_iff] at ha hb
    have := congrArg Complex.re hab
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.sub_im,
      Complex.one_im, ha.2, hb.2] at this
    nlinarith [ha.1, hb.1]

/-- `mun:stdlib/geometry/three-rays`: turning from `QA` to `QX` and on to `QB`
turns from `QA` to `QB`, give or take whole turns. -/
theorem three_rays (A B Q X : ℂ) (h1 : A ≠ Q) (h2 : B ≠ Q) (h3 : X ≠ Q) :
    ∃ k : ℤ, Complex.arg ((X - Q) / (A - Q)) + Complex.arg ((B - Q) / (X - Q)) =
      Complex.arg ((B - Q) / (A - Q)) + 2 * (k : ℝ) * Real.pi := by
  have hA : A - Q ≠ 0 := sub_ne_zero.mpr h1
  have hB : B - Q ≠ 0 := sub_ne_zero.mpr h2
  have hX : X - Q ≠ 0 := sub_ne_zero.mpr h3
  have hprod : (X - Q) / (A - Q) * ((B - Q) / (X - Q)) = (B - Q) / (A - Q) := by
    field_simp
  have hang : ((Complex.arg ((X - Q) / (A - Q)) + Complex.arg ((B - Q) / (X - Q)) : ℝ) :
      Real.Angle) = (Complex.arg ((B - Q) / (A - Q)) : Real.Angle) := by
    rw [Real.Angle.coe_add, ← Complex.arg_mul_coe_angle (div_ne_zero hX hA) (div_ne_zero hB hX),
      hprod]
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hang
  exact ⟨k, by linarith⟩

/-- `mun:stdlib/geometry/isosceles-signed-angles`: with `|AQ| = |BQ|` the base
angles are equal as signed angles, the one quotient a positive real multiple of
the other. -/
theorem isosceles_signed_angles (A B Q : ℂ) (h1 : A ≠ Q) (_h2 : B ≠ Q) (h3 : A ≠ B)
    (h4 : dist A Q = dist B Q) :
    Complex.arg ((B - A) / (Q - A)) = Complex.arg ((Q - B) / (A - B)) := by
  have ha : A - Q ≠ 0 := sub_ne_zero.mpr h1
  have hab : B - A ≠ 0 := sub_ne_zero.mpr h3.symm
  have hQA : Q - A ≠ 0 := sub_ne_zero.mpr h1.symm
  have hAB : A - B ≠ 0 := sub_ne_zero.mpr h3
  have hn : Complex.normSq (A - Q) = Complex.normSq (B - Q) := by
    rw [Complex.dist_eq, Complex.dist_eq] at h4
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, h4]
  have hc : (A - Q) * (starRingEnd ℂ) (A - Q) = (B - Q) * (starRingEnd ℂ) (B - Q) := by
    rw [Complex.mul_conj, Complex.mul_conj, hn]
  have ht : 0 < Complex.normSq (B - A) / Complex.normSq (A - Q) :=
    div_pos (Complex.normSq_pos.mpr hab) (Complex.normSq_pos.mpr ha)
  have hcA : (starRingEnd ℂ) (A - Q) ≠ 0 := (map_ne_zero _).mpr ha
  have key : (B - A) / (Q - A) = ((Complex.normSq (B - A) / Complex.normSq (A - Q) : ℝ) : ℂ)
      * ((Q - B) / (A - B)) := by
    rw [Complex.ofReal_div, ← Complex.mul_conj, ← Complex.mul_conj,
      show B - A = (B - Q) - (A - Q) by ring, show Q - A = -(A - Q) by ring,
      show Q - B = -(B - Q) by ring, show A - B = (A - Q) - (B - Q) by ring, map_sub]
    rw [show B - A = (B - Q) - (A - Q) by ring] at hab
    rw [show A - B = (A - Q) - (B - Q) by ring] at hAB
    generalize A - Q = a at ha hab hAB hc hcA ⊢
    generalize B - Q = b at ha hab hAB hc hcA ⊢
    generalize (starRingEnd ℂ) a = a' at hc hcA ⊢
    generalize (starRingEnd ℂ) b = b' at hc hcA ⊢
    field_simp
    linear_combination -hc
  rw [key, Complex.arg_real_mul _ ht]

/-- A number whose imaginary part is positive has a positive argument. -/
theorem arg_pos_of_im_pos {z : ℂ} (h : 0 < z.im) : 0 < Complex.arg z :=
  lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr h.le)
    (fun h0 => by have := (Complex.arg_eq_zero_iff.mp h0.symm).2; linarith)

/-- Seen from `C`, the segment `AB` turns the way `C` lies off the line `AB`: the
imaginary part of `(B − C)/(A − C)` is that of `(C − A)/(B − A)` over a positive
number. -/
theorem im_turn (A B C : ℂ) (hC : C - A ≠ 0) :
    Complex.im ((B - C) / (A - C)) =
      Complex.im ((C - A) / (B - A)) / Complex.normSq ((C - A) / (B - A)) := by
  have hAC : A - C ≠ 0 := by intro h; exact hC (by linear_combination -h)
  have : (B - C) / (A - C) = 1 - ((C - A) / (B - A))⁻¹ := by
    field_simp; ring
  rw [this, Complex.sub_im, Complex.inv_im, Complex.one_im]
  ring

/-- `mun:stdlib/geometry/same-side-turns-alike`: two points on one side of line
`AB` see the segment `AB` turned the same way. -/
theorem same_side_turns_alike (A B C D : ℂ)
    (h1 : 0 < Complex.im ((C - A) / (B - A)) * Complex.im ((D - A) / (B - A))) :
    0 < Complex.arg ((B - C) / (A - C)) * Complex.arg ((B - D) / (A - D)) := by
  have hne : ∀ X : ℂ, Complex.im ((X - A) / (B - A)) ≠ 0 →
      X - A ≠ 0 ∧ 0 < Complex.normSq ((X - A) / (B - A)) := by
    intro X hX
    refine ⟨fun h => hX (by simp [h]), ?_⟩
    exact Complex.normSq_pos.mpr (fun h => hX (by simp [h]))
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos h1 with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · obtain ⟨hC, nC⟩ := hne C hx.ne'
    obtain ⟨hD, nD⟩ := hne D hy.ne'
    apply mul_pos
    · exact arg_pos_of_im_pos (by rw [im_turn A B C hC]; positivity)
    · exact arg_pos_of_im_pos (by rw [im_turn A B D hD]; positivity)
  · obtain ⟨hC, nC⟩ := hne C hx.ne
    obtain ⟨hD, nD⟩ := hne D hy.ne
    apply mul_pos_of_neg_of_neg
    · exact Complex.arg_neg_iff.mpr (by rw [im_turn A B C hC]; exact div_neg_of_neg_of_pos hx nC)
    · exact Complex.arg_neg_iff.mpr (by rw [im_turn A B D hD]; exact div_neg_of_neg_of_pos hy nD)

/-- `mun:stdlib/geometry/right-angled-at-vertex`: a triangle right-angled at `R`
has its right angle at `R`, since `R` is neither `P` nor `Q`. -/
theorem right_angled_at_vertex (P Q R : ℂ) :
    Triangle P Q R ∧ (R = P ∧ EuclideanGeometry.angle Q P R = Real.pi / 2 ∨
      R = Q ∧ EuclideanGeometry.angle P Q R = Real.pi / 2 ∨
      R = R ∧ EuclideanGeometry.angle P R Q = Real.pi / 2) ↔
    Triangle P Q R ∧ EuclideanGeometry.angle P R Q = (90 : ℝ) * Real.pi / 180 := by
  rw [show (90 : ℝ) * Real.pi / 180 = Real.pi / 2 by ring]
  constructor
  · rintro ⟨hT, ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩⟩
    · exact absurd h.symm hT.2.2.1
    · exact absurd h.symm hT.2.1
    · exact ⟨hT, h⟩
  · rintro ⟨hT, h⟩
    exact ⟨hT, Or.inr (Or.inr ⟨rfl, h⟩)⟩

/-- A point whose quotient by a direction is real is the base point plus that
real multiple of the direction. -/
theorem eq_add_re_mul (P A B : ℂ) (hBA : B - A ≠ 0) (h : Complex.im ((P - A) / (B - A)) = 0) :
    P = A + (((P - A) / (B - A)).re : ℂ) * (B - A) := by
  have : (((P - A) / (B - A)).re : ℂ) = (P - A) / (B - A) := by
    apply Complex.ext <;> simp [h]
  rw [this]; field_simp; ring

/-- `y` is strictly between `x` and `z` when `x ≠ z` and `y` is `x` plus a real
fraction of the way to `z`, strictly between 0 and 1. -/
theorem sbtw_iff_exists_real (x y z : ℂ) :
    Sbtw ℝ x y z ↔ x ≠ z ∧ ∃ s : ℝ, 0 < s ∧ s < 1 ∧ y = x + s * (z - x) := by
  rw [sbtw_iff_mem_image_Ioo_and_ne]
  constructor
  · rintro ⟨⟨s, ⟨hs0, hs1⟩, rfl⟩, hxz⟩
    refine ⟨hxz, s, hs0, hs1, ?_⟩
    rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Complex.real_smul]
    ring
  · rintro ⟨hxz, s, hs0, hs1, rfl⟩
    refine ⟨⟨s, ⟨hs0, hs1⟩, ?_⟩, hxz⟩
    rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Complex.real_smul]
    ring

/-- The quotient by the direction of a point that is a real multiple of it along. -/
theorem ratio_of_eq (P A B : ℂ) (s : ℝ) (hBA : B - A ≠ 0) (h : P = A + s * (B - A)) :
    (P - A) / (B - A) = s := by
  rw [h]; field_simp; ring

/-- `def:stdlib/geometry/ray`: the ray from `A` through `B` is `A`, `B`, the points
between them and the points beyond `B`. -/
theorem mem_ray_iff (P A B : ℂ) (h1 : A ≠ B) :
    P ∈ ray A B ↔ ((P = A ∨ P = B) ∨ Sbtw ℝ A P B) ∨ Sbtw ℝ A B P := by
  have hBA : B - A ≠ 0 := sub_ne_zero.mpr h1.symm
  have hmem : P ∈ ray A B ↔
      Complex.im ((P - A) / (B - A)) = 0 ∧ 0 ≤ Complex.re ((P - A) / (B - A)) := by
    simp only [ray, Set.mem_ofPred_eq, ne_eq, h1, not_false_eq_true, true_and]
  rw [hmem, sbtw_iff_exists_real, sbtw_iff_exists_real]
  constructor
  · rintro ⟨him, hre⟩
    have hP := eq_add_re_mul P A B hBA him
    set t := ((P - A) / (B - A)).re
    rcases hre.lt_or_eq with ht | ht
    · have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
      rcases lt_trichotomy t 1 with ht1 | ht1 | ht1
      · exact Or.inl (Or.inr ⟨h1, t, ht, ht1, hP⟩)
      · left; left; right; rw [hP, ht1]; push_cast; ring
      · right
        refine ⟨fun hAP => ?_, 1 / t, by positivity, by rw [div_lt_one (by linarith)]; exact ht1, ?_⟩
        · rw [← hAP] at hP
          have : (t : ℂ) * (B - A) = 0 := by linear_combination -hP
          rcases mul_eq_zero.mp this with h | h
          · exact ht0 h
          · exact hBA h
        · rw [hP]; push_cast; field_simp; ring
    · left; left; left; rw [hP, ← ht]; simp
  · rintro (((rfl | rfl) | ⟨-, s, hs0, -, hP⟩) | ⟨hAP, s, hs0, hs1, hB⟩)
    · simp
    · rw [div_self hBA]; simp
    · rw [ratio_of_eq P A B s hBA hP]; simp [hs0.le]
    · have hPA : P - A ≠ 0 := sub_ne_zero.mpr (Ne.symm hAP)
      have hs : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
      have : (P - A) / (B - A) = ((1 / s : ℝ) : ℂ) := by
        rw [hB]; push_cast; field_simp; ring
      rw [this]; simp only [Complex.ofReal_im, Complex.ofReal_re, true_and]; positivity

/-- `mun:stdlib/geometry/line-turned`: the line through `A` and `B` is the line
through `B` and `A`. -/
theorem line_turned (A B : ℂ) : line A B = line B A := by
  ext P
  simp only [line, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h, him⟩
    have hBA : B - A ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    have hAB : A - B ≠ 0 := sub_ne_zero.mpr h
    refine ⟨Ne.symm h, ?_⟩
    have : (P - B) / (A - B) = 1 - (P - A) / (B - A) := by field_simp; ring
    rw [this, Complex.sub_im, him, Complex.one_im, sub_zero]
  · rintro ⟨h, him⟩
    have hBA : B - A ≠ 0 := sub_ne_zero.mpr h
    have hAB : A - B ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    refine ⟨Ne.symm h, ?_⟩
    have : (P - A) / (B - A) = 1 - (P - B) / (A - B) := by field_simp; ring
    rw [this, Complex.sub_im, him, Complex.one_im, sub_zero]

/-- `mun:stdlib/geometry/on-line-cases`: a point of line `QR` is `Q`, `R`, between
them, or beyond one of them, as the real quotient `(P − Q)/(R − Q)` is 0, 1,
between, above 1 or below 0. -/
theorem on_line_cases (P Q R : ℂ) (h1 : Q ≠ R) (h2 : P ∈ line Q R) :
    (((P = Q ∨ Sbtw ℝ Q P R) ∨ P = R) ∨ Sbtw ℝ Q R P) ∨ Sbtw ℝ P Q R := by
  have hRQ : R - Q ≠ 0 := sub_ne_zero.mpr h1.symm
  have hP := eq_add_re_mul P Q R hRQ h2.2
  set t := ((P - Q) / (R - Q)).re
  simp only [sbtw_iff_exists_real]
  rcases lt_trichotomy t 0 with ht | ht | ht
  · right
    refine ⟨fun hPR => ?_, -t / (1 - t), by apply div_pos <;> linarith,
      by rw [div_lt_one (by linarith)]; linarith, ?_⟩
    · rw [hPR] at hP
      have : ((t : ℂ) - 1) * (R - Q) = 0 := by linear_combination -hP
      rcases mul_eq_zero.mp this with h | h
      · have : (t : ℂ) = 1 := by linear_combination h
        have : t = 1 := by exact_mod_cast this
        linarith
      · exact hRQ h
    · have h1t : (1 : ℂ) - t ≠ 0 := by
        intro h
        have : (t : ℂ) = 1 := by linear_combination -h
        have : t = 1 := by exact_mod_cast this
        linarith
      rw [hP]; push_cast; field_simp; ring
  · left; left; left; left; rw [hP, ht]; simp
  · rcases lt_trichotomy t 1 with ht1 | ht1 | ht1
    · left; left; left; right; exact ⟨h1, t, ht, ht1, hP⟩
    · left; left; right; rw [hP, ht1]; push_cast; ring
    · left; right
      have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
      refine ⟨fun hQP => ?_, 1 / t, by positivity, by rw [div_lt_one (by linarith)]; exact ht1, ?_⟩
      · rw [← hQP] at hP
        have : (t : ℂ) * (R - Q) = 0 := by linear_combination -hP
        rcases mul_eq_zero.mp this with h | h
        · have : t = 0 := by exact_mod_cast h
          linarith
        · exact hRQ h
      · rw [hP]; push_cast; field_simp; ring

/-- `mun:stdlib/geometry/perpendicular-by-right-angle`: lines `QP` and `QR` are
perpendicular exactly when the angle at `Q` is a right angle. -/
theorem perpendicular_by_right_angle (P Q R : ℂ) (h1 : P ≠ Q) (h2 : R ≠ Q) (_h3 : P ≠ R) :
    Q ≠ P ∧ Q ≠ R ∧ Complex.re ((R - Q) / (P - Q)) = 0 ↔
      EuclideanGeometry.angle P Q R = (90 : ℝ) * Real.pi / 180 := by
  have hz : (R - Q) / (P - Q) ≠ 0 := div_ne_zero (sub_ne_zero.mpr h2) (sub_ne_zero.mpr h1)
  rw [angle_eq_abs_signed_angle P Q R h1 h2, show (90 : ℝ) * Real.pi / 180 = Real.pi / 2 by ring,
    abs_eq (by positivity), Complex.arg_eq_pi_div_two_iff, Complex.arg_eq_neg_pi_div_two_iff]
  constructor
  · rintro ⟨-, -, hre⟩
    rcases lt_trichotomy ((R - Q) / (P - Q)).im 0 with him | him | him
    · exact Or.inr ⟨hre, him⟩
    · exact absurd (Complex.ext hre him) hz
    · exact Or.inl ⟨hre, him⟩
  · rintro (⟨hre, -⟩ | ⟨hre, -⟩)
    · exact ⟨Ne.symm h1, Ne.symm h2, hre⟩
    · exact ⟨Ne.symm h1, Ne.symm h2, hre⟩

/-- The midpoint of a segment is half the sum of its ends. -/
theorem eq_half_add (A B M : ℂ) (h : Sbtw ℝ A M B ∧ dist A M = dist M B) :
    M = (A + B) / 2 := by
  obtain ⟨⟨hAB, s, hs0, hs1, hM⟩, hd⟩ := (and_congr_left' (sbtw_iff_exists_real A M B)).mp h
  have hn : 0 < ‖B - A‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hAB))
  have e1 : dist A M = s * ‖B - A‖ := by
    rw [Complex.dist_eq, hM, show A - (A + s * (B - A)) = -((s : ℂ) * (B - A)) by ring, norm_neg,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
  have e2 : dist M B = (1 - s) * ‖B - A‖ := by
    rw [Complex.dist_eq, hM,
      show A + s * (B - A) - B = -(((1 - s : ℝ) : ℂ) * (B - A)) by push_cast; ring, norm_neg,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  rw [e1, e2] at hd
  have hs : s = 1 / 2 := by
    have := mul_right_cancel₀ hn.ne' hd
    linarith
  rw [hM, hs]; push_cast; ring

/-- `mun:stdlib/geometry/midpoint-unique`: a segment has one midpoint. -/
theorem midpoint_unique (A B M N : ℂ) (h1 : Sbtw ℝ A M B ∧ dist A M = dist M B)
    (h2 : Sbtw ℝ A N B ∧ dist A N = dist N B) : M = N := by
  rw [eq_half_add A B M h1, eq_half_add A B N h2]

/-- `mun:stdlib/geometry/midpoint-determines-end`: one end and the midpoint fix
the other end. -/
theorem midpoint_determines_end (A B C M : ℂ) (h1 : Sbtw ℝ A M B ∧ dist A M = dist M B)
    (h2 : Sbtw ℝ A M C ∧ dist A M = dist M C) : B = C := by
  have e1 := eq_half_add A B M h1
  have e2 := eq_half_add A C M h2
  linear_combination 2 * e2 - 2 * e1

/-- `def:stdlib/geometry/parallel`: the directions of two lines have a real
quotient exactly when the lines are one line or never meet. -/
theorem parallel (A B C D : ℂ) (h1 : A ≠ B) (h2 : C ≠ D) :
    Complex.im ((B - A) / (D - C)) = 0 ↔ line A B = line C D ∨
      ¬ (∃ X ∈ (Set.univ : Set ℂ), X ∈ line A B ∧ X ∈ line C D) := by
  have hBA : B - A ≠ 0 := sub_ne_zero.mpr h1.symm
  have hDC : D - C ≠ 0 := sub_ne_zero.mpr h2.symm
  have memAB : ∀ X, X ∈ line A B ↔ Complex.im ((X - A) / (B - A)) = 0 := by
    intro X; simp [line, h1]
  have memCD : ∀ X, X ∈ line C D ↔ Complex.im ((X - C) / (D - C)) = 0 := by
    intro X; simp [line, h2]
  have split : ∀ X Y : ℂ, Complex.im ((X - Y) / (D - C)) =
      Complex.im ((X - C) / (D - C)) - Complex.im ((Y - C) / (D - C)) := by
    intro X Y
    rw [← Complex.sub_im]; congr 1; field_simp; ring
  constructor
  · intro him
    by_cases hX : ∃ X ∈ (Set.univ : Set ℂ), X ∈ line A B ∧ X ∈ line C D
    · left
      obtain ⟨X, -, hXA, hXC⟩ := hX
      rw [memAB] at hXA
      rw [memCD] at hXC
      set t := ((B - A) / (D - C)).re
      have ht : (B - A) / (D - C) = (t : ℂ) := by apply Complex.ext <;> simp [t, him]
      have ht0 : t ≠ 0 := by
        intro h0; rw [h0, Complex.ofReal_zero] at ht
        exact div_ne_zero hBA hDC ht
      have hBAt : B - A = t * (D - C) := by rw [← ht]; field_simp
      have conv : ∀ Y : ℂ,
          Complex.im ((Y - A) / (B - A)) = Complex.im ((Y - A) / (D - C)) / t := by
        intro Y; rw [hBAt, ← Complex.div_ofReal_im]; congr 1; field_simp
      have hXA' : Complex.im ((X - A) / (D - C)) = 0 := by
        have := conv X; rw [hXA] at this
        exact (div_eq_zero_iff.mp this.symm).resolve_right ht0
      have hAC : Complex.im ((A - C) / (D - C)) = 0 := by
        have := split X A; rw [hXA', hXC] at this; linarith
      ext Y
      rw [memAB, memCD, conv, split Y A, hAC, sub_zero, div_eq_zero_iff]
      simp [ht0]
    · right; exact hX
  · rintro (heq | hno)
    · have hA : A ∈ line C D := heq ▸ (memAB A).mpr (by simp)
      have hB : B ∈ line C D := heq ▸ (memAB B).mpr (by simp [div_self hBA])
      rw [memCD] at hA hB
      rw [split, hA, hB, sub_zero]
    · by_contra him
      apply hno
      set s := -Complex.im ((A - C) / (D - C)) / Complex.im ((B - A) / (D - C))
      refine ⟨A + s * (B - A), Set.mem_univ _, ?_, ?_⟩
      · rw [memAB, ratio_of_eq _ A B s hBA rfl, Complex.ofReal_im]
      · rw [memCD]
        have : (A + s * (B - A) - C) / (D - C) =
            (A - C) / (D - C) + s * ((B - A) / (D - C)) := by
          field_simp; ring
        rw [this, Complex.add_im, Complex.im_ofReal_mul]
        simp only [s]
        field_simp
        ring

/-- `mun:stdlib/geometry/collinear-by-coordinates`: three points are collinear
exactly when the cross product of the differences from the first is 0. -/
theorem collinear_by_coordinates (a b c d e f : ℝ) :
    Collinear ℝ {Complex.mk a b, Complex.mk c d, Complex.mk e f} ↔
      (c - a) * (f - b) = (e - a) * (d - b) := by
  by_cases hAB : Complex.mk a b = Complex.mk c d
  · obtain ⟨rfl, rfl⟩ : a = c ∧ b = d := by simpa using hAB
    simp [collinear_pair]
  · rw [← mem_line_iff_collinear _ _ _ hAB]
    simp only [line, Set.mem_ofPred_eq, ne_eq, hAB, not_false_eq_true, true_and]
    have hn : 0 < Complex.normSq (Complex.mk c d - Complex.mk a b) :=
      Complex.normSq_pos.mpr (sub_ne_zero.mpr (Ne.symm hAB))
    rw [Complex.div_im, ← sub_div, div_eq_zero_iff, or_iff_left hn.ne']
    simp only [Complex.sub_re, Complex.sub_im]
    constructor <;> intro h <;> linarith

/-- `mun:stdlib/geometry/between-by-coordinates`: `(c, d)` is strictly between
`(a, b)` and `(e, f)` exactly when the differences from it are parallel and point
opposite ways. -/
theorem between_by_coordinates (a b c d e f : ℝ) :
    Sbtw ℝ (Complex.mk a b) (Complex.mk c d) (Complex.mk e f) ↔
      (a - c) * (f - d) = (e - c) * (b - d) ∧ (a - c) * (e - c) + (b - d) * (f - d) < 0 := by
  rw [sbtw_iff_exists_real]
  constructor
  · rintro ⟨hne, t, ht0, ht1, hY⟩
    have hre := congrArg Complex.re hY
    have him := congrArg Complex.im hY
    simp at hre him
    have hpos : 0 < (e - a) ^ 2 + (f - b) ^ 2 := by
      rcases (add_nonneg (sq_nonneg (e - a)) (sq_nonneg (f - b))).lt_or_eq with h | h
      · exact h
      · exfalso; apply hne
        have h1 : e - a = 0 := by nlinarith [sq_nonneg (e - a), sq_nonneg (f - b)]
        have h2 : f - b = 0 := by nlinarith [sq_nonneg (e - a), sq_nonneg (f - b)]
        apply Complex.ext <;> simp <;> linarith
    refine ⟨by rw [hre, him]; ring, ?_⟩
    rw [hre, him]
    have : 0 < t * (1 - t) * ((e - a) ^ 2 + (f - b) ^ 2) :=
      mul_pos (mul_pos ht0 (by linarith)) hpos
    nlinarith
  · rintro ⟨hcross, hdot⟩
    have hN : 0 < (a - c) ^ 2 + (b - d) ^ 2 := by
      rcases (add_nonneg (sq_nonneg (a - c)) (sq_nonneg (b - d))).lt_or_eq with h | h
      · exact h
      · have h1 : a - c = 0 := by nlinarith [sq_nonneg (a - c), sq_nonneg (b - d)]
        have h2 : b - d = 0 := by nlinarith [sq_nonneg (a - c), sq_nonneg (b - d)]
        rw [h1, h2] at hdot; linarith
    have hden : 0 < (a - c) ^ 2 + (b - d) ^ 2 - ((a - c) * (e - c) + (b - d) * (f - d)) := by
      linarith
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = ((a - c) ^ 2 + (b - d) ^ 2) /
        ((a - c) ^ 2 + (b - d) ^ 2 - ((a - c) * (e - c) + (b - d) * (f - d))) := ⟨_, rfl⟩
    refine ⟨fun h => ?_, s, hs ▸ div_pos hN hden, hs ▸ (div_lt_one hden).mpr (by linarith), ?_⟩
    · have h1 : a = e := by simpa using congrArg Complex.re h
      have h2 : b = f := by simpa using congrArg Complex.im h
      subst h1 h2
      nlinarith [sq_nonneg (a - c), sq_nonneg (b - d)]
    · apply Complex.ext
      · simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.sub_re]
        rw [hs]
        field_simp
        linear_combination (b - d) * hcross
      · simp only [Complex.add_im, Complex.im_ofReal_mul, Complex.sub_im]
        rw [hs]
        field_simp
        linear_combination -(a - c) * hcross

/-- `mun:stdlib/geometry/triangle-on-side`: a point strictly inside side `QR`
makes a triangle with `P` and `Q`. -/
theorem triangle_on_side (P Q R S : ℂ) (h1 : Triangle P Q R) (h2 : Sbtw ℝ Q S R) :
    Triangle P Q S := by
  obtain ⟨hPQ, -, -, hcol⟩ := h1
  have hc : Collinear ℝ ({Q, S, R} : Set ℂ) := h2.wbtw.collinear
  refine ⟨hPQ, h2.left_ne, ?_, fun h => hcol ?_⟩
  · rintro rfl
    exact hcol ((collinear_swap_12 P Q R).mpr (by simpa using hc))
  · have h' : Collinear ℝ (insert P ({Q, S, R} : Set ℂ)) :=
      (hc.collinear_insert_iff_of_ne (by simp) (by simp) h2.left_ne).mpr h
    exact h'.subset (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto)

/-- `mun:stdlib/geometry/segment-addition`: a point between two others splits
their distance in two. -/
theorem segment_addition (P Q S : ℂ) (h1 : Sbtw ℝ P S Q) : dist P S + dist S Q = dist P Q :=
  h1.wbtw.dist_add_dist

/-- `thm:stdlib/geometry/law-of-sines`: each side times the sine of the angle at
one of its ends is the same for the other side at that angle's vertex. -/
theorem law_of_sines (P Q R : ℂ) (_h1 : Triangle P Q R) :
    dist P Q * Real.sin (EuclideanGeometry.angle P Q R) =
      dist P R * Real.sin (EuclideanGeometry.angle Q R P) := by
  have := EuclideanGeometry.sin_angle_mul_dist_eq_sin_angle_mul_dist R Q P
  rw [EuclideanGeometry.angle_comm R Q P, EuclideanGeometry.angle_comm P R Q,
    dist_comm Q P] at this
  linear_combination this

/-- The size of the sine of the signed angle at `R` is the sine of the angle at `R`. -/
theorem abs_sin_arg_eq_sin_angle (P Q R : ℂ) (h1 : P ≠ R) (h2 : Q ≠ R) :
    |Real.sin (Complex.arg ((P - R) / (Q - R)))| = Real.sin (EuclideanGeometry.angle Q R P) := by
  rw [angle_eq_abs_signed_angle Q R P h2 h1, Real.abs_sin_eq_sin_abs_of_abs_le_pi
    (abs_le.mpr ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩)]

/-- `thm:stdlib/geometry/area-by-sine`: the area is half two sides times the sine
of the angle between them. -/
theorem area_by_sine (P Q R : ℂ) (h1 : P ≠ R) (h2 : Q ≠ R) (_h3 : Q ≠ P) :
    1 / 2 * (dist Q R * dist P R) * abs (Real.sin (Complex.arg ((P - R) / (Q - R)))) =
      1 / 2 * (dist Q R * dist P R) * Real.sin (EuclideanGeometry.angle Q R P) := by
  rw [abs_sin_arg_eq_sin_angle P Q R h1 h2]

/-- `axi:stdlib/geometry/area-positive`: a triangle has a positive area, its two
sides at `R` positive and the sine of the angle there positive. -/
theorem area_positive (P Q R : ℂ) (h1 : Triangle P Q R) :
    0 < 1 / 2 * (dist Q R * dist P R) * abs (Real.sin (Complex.arg ((P - R) / (Q - R)))) := by
  have hs := EuclideanGeometry.sin_pos_of_not_collinear ((triangle_rot_231 P Q R).mp h1).2.2.2
  obtain ⟨-, hQR, hPR, -⟩ := h1
  rw [abs_sin_arg_eq_sin_angle P Q R hPR hQR]
  have := dist_pos.mpr hQR
  have := dist_pos.mpr hPR
  positivity

/-- `thm:stdlib/geometry/law-of-cosines`: the side opposite `Q` from the two
sides at `Q` and the angle between them. -/
theorem law_of_cosines (P Q R : ℂ) (_h1 : P ≠ Q) (_h2 : R ≠ Q) (_h3 : P ≠ R) :
    dist R P ^ 2 = dist P Q ^ 2 + dist Q R ^ 2 -
      2 * (dist P Q * dist Q R * Real.cos (EuclideanGeometry.angle P Q R)) := by
  rw [dist_comm R P, dist_comm Q R]
  linear_combination EuclideanGeometry.law_cos P Q R

/-- `thm:stdlib/geometry/heron`: the area is the square root of
`s(s − a)(s − b)(s − c)`, which the law of cosines and `sin² + cos² = 1` make
the area's square. -/
theorem heron (P Q R : ℂ) (s : ℝ) (h2 : P ≠ R) (h3 : Q ≠ R)
    (h4 : s = (dist Q R + dist P R + dist P Q) / 2) :
    ((1 / 2 * (dist Q R * dist P R) * abs (Real.sin (Complex.arg ((P - R) / (Q - R)))) : ℝ) : ℂ) =
      ((s : ℂ) * ((s : ℂ) - (dist Q R : ℂ)) * (((s : ℂ) - (dist P R : ℂ)) *
        ((s : ℂ) - (dist P Q : ℂ)))) ^ (1 / 2 : ℂ) := by
  rw [abs_sin_arg_eq_sin_angle P Q R h2 h3]
  have hA : 0 ≤ 1 / 2 * (dist Q R * dist P R) * Real.sin (EuclideanGeometry.angle Q R P) :=
    mul_nonneg (by positivity) (Real.sin_nonneg_of_nonneg_of_le_pi
      (EuclideanGeometry.angle_nonneg _ _ _) (EuclideanGeometry.angle_le_pi _ _ _))
  have hlc := EuclideanGeometry.law_cos Q R P
  rw [dist_comm Q P] at hlc
  have hsc := Real.sin_sq_add_cos_sq (EuclideanGeometry.angle Q R P)
  have key : s * (s - dist Q R) * ((s - dist P R) * (s - dist P Q)) =
      (1 / 2 * (dist Q R * dist P R) * Real.sin (EuclideanGeometry.angle Q R P)) ^ 2 := by
    rw [h4]
    linear_combination (1 / 16 * (dist Q R ^ 2 + dist P R ^ 2 - dist P Q ^ 2 +
      2 * dist Q R * dist P R * Real.cos (EuclideanGeometry.angle Q R P))) * hlc -
      (1 / 4 * dist Q R ^ 2 * dist P R ^ 2) * hsc
  have hc : (s : ℂ) * ((s : ℂ) - (dist Q R : ℂ)) * (((s : ℂ) - (dist P R : ℂ)) *
      ((s : ℂ) - (dist P Q : ℂ))) =
      (((1 / 2 * (dist Q R * dist P R) * Real.sin (EuclideanGeometry.angle Q R P)) ^ 2 : ℝ) :
        ℂ) := by
    rw [← key]; push_cast; ring
  rw [hc, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (sq_nonneg _), ← Real.sqrt_eq_rpow, Real.sqrt_sq hA]

/-- `mun:stdlib/geometry/right-angle-triangle`: the arms of a right angle are not
on one line, as collinear points make an angle of 0 or `π`. -/
theorem right_angle_triangle (P Q R : ℂ) (h1 : P ≠ Q) (h2 : R ≠ Q)
    (h3 : EuclideanGeometry.angle P Q R = (90 : ℝ) * Real.pi / 180) (h4 : P ≠ R) :
    Triangle P Q R := by
  have hpi := Real.pi_pos
  refine ⟨h1, Ne.symm h2, h4, fun h => ?_⟩
  rcases EuclideanGeometry.collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi.mp h with
    h | h | h | h
  · exact h1 h
  · exact h2 h
  · rw [h] at h3; linarith
  · rw [h] at h3; linarith

/-- `mun:stdlib/geometry/cosine-right-triangle`: with a right angle at `R`, the
side `QR` is the hypotenuse times the cosine of the angle at `Q`. -/
theorem cosine_right_triangle (P Q R : ℂ) (_h1 : P ≠ R) (_h2 : Q ≠ R)
    (h3 : EuclideanGeometry.angle P R Q = (90 : ℝ) * Real.pi / 180) (_h4 : P ≠ Q) :
    dist Q R = dist Q P * Real.cos (EuclideanGeometry.angle R Q P) := by
  rw [← EuclideanGeometry.cos_angle_mul_dist_of_angle_eq_pi_div_two (h3.trans (by ring)),
    dist_comm Q P, mul_comm]

/-- `mun:stdlib/geometry/angle-addition`: a point strictly inside side `AB` splits
the angle at `C` in two. The signed angles from `CA` to `CM` and from `CM` to `CB`
have the sign of the one from `CA` to `CB` and add to it up to whole turns, and
their bounds leave no whole turn. -/
theorem angle_addition (A B C M : ℂ) (h1 : Triangle A B C) (h2 : Sbtw ℝ A M B) (h3 : C ≠ M) :
    EuclideanGeometry.angle A C M + EuclideanGeometry.angle M C B =
      EuclideanGeometry.angle A C B := by
  obtain ⟨-, hBC, hAC, hcol⟩ := h1
  have hA : A - C ≠ 0 := sub_ne_zero.mpr hAC
  have hM : M - C ≠ 0 := sub_ne_zero.mpr (Ne.symm h3)
  rw [angle_eq_abs_signed_angle A C M hAC (Ne.symm h3),
    angle_eq_abs_signed_angle M C B (Ne.symm h3) hBC,
    angle_eq_abs_signed_angle A C B hAC hBC]
  obtain ⟨k, hk⟩ := three_rays A B C M hAC hBC (Ne.symm h3)
  obtain ⟨-, t, ht0, ht1, hMt⟩ := (sbtw_iff_exists_real A M B).mp h2
  have hq1 : (M - C) / (A - C) = ((1 - t : ℝ) : ℂ) + t * ((B - C) / (A - C)) := by
    rw [hMt]; push_cast; field_simp; ring
  have hq2 : (B - C) / (M - C) = (B - C) / (A - C) / ((M - C) / (A - C)) := by
    field_simp
  have hzim : ((B - C) / (A - C)).im ≠ 0 := by
    intro h
    exact hcol ((collinear_rot_312 A B C).mpr
      ((mem_line_iff_collinear C A B (Ne.symm hAC)).mp ⟨Ne.symm hAC, h⟩))
  have im1 : ((M - C) / (A - C)).im = t * ((B - C) / (A - C)).im := by
    rw [hq1]; simp
  have re1 : ((M - C) / (A - C)).re = (1 - t) + t * ((B - C) / (A - C)).re := by
    rw [hq1]; simp
  have hn : 0 < Complex.normSq ((M - C) / (A - C)) :=
    Complex.normSq_pos.mpr (div_ne_zero hM hA)
  have im2 : ((B - C) / (M - C)).im =
      (1 - t) * ((B - C) / (A - C)).im / Complex.normSq ((M - C) / (A - C)) := by
    rw [hq2, Complex.div_im, im1, re1]; ring
  have hpi := Real.pi_pos
  have l1 := Complex.neg_pi_lt_arg ((M - C) / (A - C))
  have u1 := Complex.arg_le_pi ((M - C) / (A - C))
  have l2 := Complex.neg_pi_lt_arg ((B - C) / (M - C))
  have u2 := Complex.arg_le_pi ((B - C) / (M - C))
  have l3 := Complex.neg_pi_lt_arg ((B - C) / (A - C))
  have u3 := Complex.arg_le_pi ((B - C) / (A - C))
  rcases lt_or_gt_of_ne hzim with hneg | hpos
  · have a1 : Complex.arg ((M - C) / (A - C)) < 0 :=
      Complex.arg_neg_iff.mpr (by rw [im1]; nlinarith)
    have a2 : Complex.arg ((B - C) / (M - C)) < 0 :=
      Complex.arg_neg_iff.mpr (by rw [im2]; exact div_neg_of_neg_of_pos (by nlinarith) hn)
    have a3 : Complex.arg ((B - C) / (A - C)) < 0 := Complex.arg_neg_iff.mpr hneg
    have kl : (k : ℝ) < 1 := by by_contra h; rw [not_lt] at h; nlinarith
    have kg : (-1 : ℝ) < k := by by_contra h; rw [not_lt] at h; nlinarith
    have hk0 : k = 0 := by
      have : k < 1 := by exact_mod_cast kl
      have : -1 < k := by exact_mod_cast kg
      omega
    rw [hk0] at hk
    rw [abs_of_neg a1, abs_of_neg a2, abs_of_neg a3]
    push_cast at hk
    linarith
  · have a1 : 0 < Complex.arg ((M - C) / (A - C)) :=
      arg_pos_of_im_pos (by rw [im1]; positivity)
    have a2 : 0 < Complex.arg ((B - C) / (M - C)) :=
      arg_pos_of_im_pos (by rw [im2]; exact div_pos (mul_pos (by linarith) hpos) hn)
    have a3 : 0 < Complex.arg ((B - C) / (A - C)) := arg_pos_of_im_pos hpos
    have kl : (k : ℝ) < 1 := by by_contra h; rw [not_lt] at h; nlinarith
    have kg : (-1 : ℝ) < k := by by_contra h; rw [not_lt] at h; nlinarith
    have hk0 : k = 0 := by
      have : k < 1 := by exact_mod_cast kl
      have : -1 < k := by exact_mod_cast kg
      omega
    rw [hk0] at hk
    rw [abs_of_pos a1, abs_of_pos a2, abs_of_pos a3]
    push_cast at hk
    linarith

/-- `axi:stdlib/geometry/side-angle-side`: two sides and the angle between them
fix the triangle's other side and angles. -/
theorem side_angle_side (P P' Q Q' R R' : ℂ) (_h1 : Triangle P Q R) (_h2 : Triangle P' Q' R')
    (h3 : dist P Q = dist P' Q')
    (h4 : EuclideanGeometry.angle P Q R = EuclideanGeometry.angle P' Q' R')
    (h5 : dist Q R = dist Q' R') :
    dist P Q = dist P' Q' ∧ dist Q R = dist Q' R' ∧ dist R P = dist R' P' ∧
      EuclideanGeometry.angle P Q R = EuclideanGeometry.angle P' Q' R' ∧
      EuclideanGeometry.angle Q R P = EuclideanGeometry.angle Q' R' P' ∧
      EuclideanGeometry.angle R P Q = EuclideanGeometry.angle R' P' Q' := by
  have h := EuclideanGeometry.side_angle_side h4 h3 h5
  refine ⟨h3, h5, by simpa using h.dist_eq 2 0, h4, ?_, ?_⟩
  · simpa using EuclideanGeometry.angle_eq_of_congruent h 1 2 0
  · simpa using EuclideanGeometry.angle_eq_of_congruent h 2 0 1

/-- `axi:stdlib/geometry/line-uniqueness`: two points of a line, apart, give that line. -/
theorem line_uniqueness (A B C D : ℂ) (h1 : A ≠ B) (h2 : C ≠ D)
    (h3 : A ∈ line C D) (h4 : B ∈ line C D) : line A B = line C D := by
  have hDC : D - C ≠ 0 := sub_ne_zero.mpr h2.symm
  have hA := eq_add_re_mul A C D hDC h3.2
  have hB := eq_add_re_mul B C D hDC h4.2
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = ((A - C) / (D - C)).re := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = ((B - C) / (D - C)).re := ⟨_, rfl⟩
  rw [← ha] at hA
  rw [← hb] at hB
  have hba : (b : ℂ) - a ≠ 0 := by
    intro h; apply h1; rw [hA, hB, show (b : ℂ) = a by linear_combination h]
  have hba' : b - a ≠ 0 := by exact_mod_cast hba
  ext X
  simp only [line, Set.mem_ofPred_eq, h1, h2, ne_eq, not_false_eq_true, true_and]
  have hBA' : B - A = ((b - a : ℝ) : ℂ) * (D - C) := by rw [hA, hB]; push_cast; ring
  have hXA : X - A = ((X - C) / (D - C) - a) * (D - C) := by rw [hA]; field_simp; ring
  have : (X - A) / (B - A) = ((X - C) / (D - C) - a) / ((b - a : ℝ) : ℂ) := by
    rw [hXA, hBA', mul_div_mul_right _ _ hDC]
  rw [this, Complex.div_ofReal_im, Complex.sub_im, Complex.ofReal_im, sub_zero, div_eq_zero_iff]
  simp [hba']

/-- `axi:stdlib/geometry/three-points`: `0`, `1` and `i` form a triangle. -/
theorem three_points :
    ∃ P ∈ (Set.univ : Set ℂ), ∃ Q ∈ (Set.univ : Set ℂ), ∃ R ∈ (Set.univ : Set ℂ),
      Triangle P Q R := by
  refine ⟨0, trivial, 1, trivial, Complex.I, trivial, zero_ne_one, ?_, ?_, ?_⟩
  · intro h; have := congrArg Complex.im h; simp at this
  · intro h; have := congrArg Complex.im h; simp at this
  · rw [← mem_line_iff_collinear 0 1 Complex.I zero_ne_one]
    simp [line]

/-- The ruler along line `AB` (the real quotient by `B − A`, scaled by `|AB|`) is one to
one and onto the reals, and measures distance along the line. -/
theorem ruler_props (A B : ℂ) (h1 : A ≠ B) :
    Set.InjOn (fun P => ((P - A) / (B - A)).re * dist A B) (line A B) ∧
    Set.SurjOn (fun P => ((P - A) / (B - A)).re * dist A B) (line A B) Set.univ ∧
    ∀ P ∈ line A B, ∀ Q ∈ line A B, dist P Q =
      |((P - A) / (B - A)).re * dist A B - ((Q - A) / (B - A)).re * dist A B| := by
  have hBA : B - A ≠ 0 := sub_ne_zero.mpr h1.symm
  have hd : 0 < dist A B := dist_pos.mpr h1
  refine ⟨?_, ?_, ?_⟩
  · intro P hP Q hQ h
    have h' := mul_right_cancel₀ hd.ne' h
    rw [eq_add_re_mul P A B hBA hP.2, eq_add_re_mul Q A B hBA hQ.2, h']
  · intro y _
    refine ⟨A + ((y / dist A B : ℝ) : ℂ) * (B - A), ⟨h1, ?_⟩, ?_⟩
    · rw [ratio_of_eq _ A B _ hBA rfl, Complex.ofReal_im]
    · simp only
      rw [ratio_of_eq _ A B _ hBA rfl, Complex.ofReal_re]
      field_simp
  · intro P hP Q hQ
    have e : P - Q = ((((P - A) / (B - A)).re - ((Q - A) / (B - A)).re : ℝ) : ℂ) * (B - A) := by
      conv_lhs => rw [eq_add_re_mul P A B hBA hP.2, eq_add_re_mul Q A B hBA hQ.2]
      push_cast; ring
    rw [Complex.dist_eq, e, norm_mul, Complex.norm_real, Real.norm_eq_abs, ← Complex.dist_eq,
      dist_comm, ← sub_mul, abs_mul, abs_of_pos hd]

/-- `axi:stdlib/geometry/ruler`: a line has a ruler. -/
theorem ruler (A B : ℂ) (h1 : A ≠ B) :
    ∃ f : ℂ → ℝ, Set.MapsTo f (line A B) (Set.univ : Set ℝ) ∧
      ((Set.MapsTo f (line A B) (Set.univ : Set ℝ) ∧ Set.InjOn f (line A B) ∧
        Set.SurjOn f (line A B) (Set.univ : Set ℝ)) ∧
      (∀ P ∈ line A B, ∀ Q ∈ line A B, dist P Q = abs (f P - f Q))) := by
  obtain ⟨hi, hs, hd⟩ := ruler_props A B h1
  exact ⟨_, fun _ _ => trivial, ⟨fun _ _ => trivial, hi, hs⟩, hd⟩

/-- `axi:stdlib/geometry/ruler-placement`: a line has a ruler with `A` at 0 and `B`
positive. -/
theorem ruler_placement (A B : ℂ) (h1 : A ≠ B) :
    ∃ f : ℂ → ℝ, Set.MapsTo f (line A B) (Set.univ : Set ℝ) ∧
      ((((Set.MapsTo f (line A B) (Set.univ : Set ℝ) ∧ Set.InjOn f (line A B) ∧
        Set.SurjOn f (line A B) (Set.univ : Set ℝ)) ∧ f A = 0) ∧ 0 < f B) ∧
      (∀ P ∈ line A B, ∀ Q ∈ line A B, dist P Q = abs (f P - f Q))) := by
  have hBA : B - A ≠ 0 := sub_ne_zero.mpr h1.symm
  obtain ⟨hi, hs, hd⟩ := ruler_props A B h1
  refine ⟨_, fun _ _ => trivial, ⟨⟨⟨fun _ _ => trivial, hi, hs⟩, by simp⟩, ?_⟩, hd⟩
  simp only [div_self hBA, Complex.one_re, one_mul]
  exact dist_pos.mpr h1

/-- The line from `P` through a point `C` whose step from `P` is parallel to `AB` is
the set of points whose step from `P` is parallel to `AB`. -/
theorem line_eq_of_parallel (A B C P : ℂ) (h1 : A ≠ B) (h3 : P ≠ C)
    (h5 : Complex.im ((C - P) / (B - A)) = 0) :
    line P C = {X | Complex.im ((X - P) / (B - A)) = 0} := by
  have hBA : B - A ≠ 0 := sub_ne_zero.mpr h1.symm
  have hCP : C - P ≠ 0 := sub_ne_zero.mpr h3.symm
  obtain ⟨c, hc⟩ : ∃ c : ℝ, (C - P) / (B - A) = (c : ℂ) :=
    ⟨((C - P) / (B - A)).re, by apply Complex.ext <;> simp [h5]⟩
  have hc0 : (c : ℂ) ≠ 0 := by rw [← hc]; exact div_ne_zero hCP hBA
  have hc0' : c ≠ 0 := by exact_mod_cast hc0
  have hCPc : C - P = c * (B - A) := by rw [← hc]; field_simp
  ext X
  simp only [line, Set.mem_ofPred_eq, h3, ne_eq, not_false_eq_true, true_and]
  have conv : Complex.im ((X - P) / (C - P)) = Complex.im ((X - P) / (B - A)) / c := by
    rw [hCPc, ← Complex.div_ofReal_im]; congr 1; field_simp
  rw [conv, div_eq_zero_iff]
  simp [hc0']

/-- `axi:stdlib/geometry/parallel-uniqueness`: through a point off a line there is one
parallel to it. -/
theorem parallel_uniqueness (A B C D P : ℂ) (h1 : A ≠ B) (_h2 : ¬ P ∈ line A B) (h3 : P ≠ C)
    (h4 : P ≠ D) (h5 : Complex.im ((C - P) / (B - A)) = 0)
    (h6 : Complex.im ((D - P) / (B - A)) = 0) : line P C = line P D := by
  rw [line_eq_of_parallel A B C P h1 h3 h5, line_eq_of_parallel A B D P h1 h4 h6]

/-- `axi:stdlib/geometry/plane-separation`: two points off a line are on one side of
it or on opposite sides. -/
theorem plane_separation (A B P Q : ℂ) (h1 : A ≠ B) (h2 : ¬ P ∈ line A B)
    (h3 : ¬ Q ∈ line A B) :
    0 < Complex.im ((P - A) / (B - A)) * Complex.im ((Q - A) / (B - A)) ∨
      Complex.im ((P - A) / (B - A)) * Complex.im ((Q - A) / (B - A)) < 0 := by
  have hP : Complex.im ((P - A) / (B - A)) ≠ 0 := fun h => h2 ⟨h1, h⟩
  have hQ : Complex.im ((Q - A) / (B - A)) ≠ 0 := fun h => h3 ⟨h1, h⟩
  rcases lt_or_gt_of_ne (mul_ne_zero hP hQ) with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- The quotient by `B − A` of a point a real fraction of the way from `P` to `Q`. -/
theorem ratio_along (A B P Q X : ℂ) (s : ℝ) (hBA : B - A ≠ 0) (hX : X = P + s * (Q - P)) :
    (X - A) / (B - A) =
      (P - A) / (B - A) + s * ((Q - A) / (B - A) - (P - A) / (B - A)) := by
  rw [hX]; field_simp; ring

/-- `axi:stdlib/geometry/plane-separation-convex`: a point between two points on one
side of a line is on that side. -/
theorem plane_separation_convex (A B P Q X : ℂ) (h1 : A ≠ B)
    (h2 : 0 < Complex.im ((P - A) / (B - A)) * Complex.im ((Q - A) / (B - A)))
    (h3 : Sbtw ℝ P X Q) :
    0 < Complex.im ((X - A) / (B - A)) * Complex.im ((P - A) / (B - A)) := by
  obtain ⟨-, s, hs0, hs1, hX⟩ := (sbtw_iff_exists_real P X Q).mp h3
  have hBA : B - A ≠ 0 := sub_ne_zero.mpr h1.symm
  rw [ratio_along A B P Q X s hBA hX, Complex.add_im, Complex.im_ofReal_mul, Complex.sub_im]
  have hp : Complex.im ((P - A) / (B - A)) ≠ 0 := by
    intro h; rw [h, zero_mul] at h2; exact lt_irrefl 0 h2
  have hp2 : 0 < Complex.im ((P - A) / (B - A)) ^ 2 := by positivity
  nlinarith [mul_pos (sub_pos.mpr hs1) hp2, mul_pos hs0 h2]

/-- `axi:stdlib/geometry/plane-separation-crossing`: the segment between points on
opposite sides of a line meets the line. -/
theorem plane_separation_crossing (A B P Q : ℂ) (h1 : A ≠ B)
    (h2 : Complex.im ((P - A) / (B - A)) * Complex.im ((Q - A) / (B - A)) < 0) :
    ∃ X ∈ (Set.univ : Set ℂ), X ∈ line A B ∧ Sbtw ℝ P X Q := by
  have hBA : B - A ≠ 0 := sub_ne_zero.mpr h1.symm
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = Complex.im ((P - A) / (B - A)) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = Complex.im ((Q - A) / (B - A)) := ⟨_, rfl⟩
  rw [← hp, ← hq] at h2
  have hp0 : p ≠ 0 := by rintro rfl; simp at h2
  have hp2 : 0 < p ^ 2 := by positivity
  have hden : 0 < p ^ 2 - p * q := by linarith
  have hpq : p - q ≠ 0 := by
    intro h; have : p * (p - q) = 0 := by rw [h, mul_zero]
    nlinarith
  have hPQ : P ≠ Q := by rintro rfl; rw [← hq] at hp; rw [hp] at h2; nlinarith
  refine ⟨P + ((p ^ 2 / (p ^ 2 - p * q) : ℝ) : ℂ) * (Q - P), trivial, ⟨h1, ?_⟩, ?_⟩
  · rw [ratio_along A B P Q _ _ hBA rfl, Complex.add_im, Complex.im_ofReal_mul, Complex.sub_im,
      ← hp, ← hq]
    field_simp; ring
  · rw [sbtw_iff_exists_real]
    exact ⟨hPQ, _, div_pos hp2 hden, (div_lt_one hden).mpr (by linarith), rfl⟩

/-- `axi:stdlib/geometry/angle-construction`: on the side of `AB` where `C` is, a ray
from `A` makes any angle strictly between 0 and `π` with `AB`. -/
theorem angle_construction (A B C : ℂ) (x : ℝ) (h2 : Triangle A B C)
    (h3 : (0 : ℝ) * Real.pi / 180 < x) (h4 : x < (180 : ℝ) * Real.pi / 180) :
    ∃ D ∈ (Set.univ : Set ℂ), 0 < Complex.im ((D - A) / (B - A)) * Complex.im ((C - A) / (B - A)) ∧
      EuclideanGeometry.angle B A D = x := by
  obtain ⟨hAB, -, -, hcol⟩ := h2
  have hBA : B - A ≠ 0 := sub_ne_zero.mpr hAB.symm
  have hx0 : 0 < x := by linarith
  have hxpi : x < Real.pi := by linarith
  have hc : Complex.im ((C - A) / (B - A)) ≠ 0 :=
    fun h => hcol ((mem_line_iff_collinear A B C hAB).mp ⟨hAB, h⟩)
  have hsin := Real.sin_pos_of_pos_of_lt_pi hx0 hxpi
  obtain ⟨θ, hθ, habs, hsign⟩ : ∃ θ : ℝ, θ ∈ Set.Ioc (-Real.pi) Real.pi ∧ |θ| = x ∧
      0 < Real.sin θ * Complex.im ((C - A) / (B - A)) := by
    rcases lt_or_gt_of_ne hc with h | h
    · refine ⟨-x, ⟨by linarith, by linarith⟩, by rw [abs_neg, abs_of_pos hx0], ?_⟩
      rw [Real.sin_neg]; nlinarith
    · exact ⟨x, ⟨by linarith, by linarith⟩, abs_of_pos hx0, mul_pos hsin h⟩
  have hz : (Complex.cos θ + Complex.sin θ * Complex.I).im = Real.sin θ := by
    simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hq : (A + (Complex.cos θ + Complex.sin θ * Complex.I) * (B - A) - A) / (B - A) =
      Complex.cos θ + Complex.sin θ * Complex.I := by field_simp; ring
  have hDA : A + (Complex.cos θ + Complex.sin θ * Complex.I) * (B - A) ≠ A := by
    intro h
    rw [h, sub_self, zero_div] at hq
    have := congrArg Complex.im hq
    rw [hz, Complex.zero_im] at this
    rw [← this, zero_mul] at hsign
    exact lt_irrefl 0 hsign
  refine ⟨A + (Complex.cos θ + Complex.sin θ * Complex.I) * (B - A), trivial, ?_, ?_⟩
  · rw [hq, hz]; exact hsign
  · rw [angle_eq_abs_signed_angle B A _ hAB.symm hDA, hq, Complex.arg_cos_add_sin_mul_I hθ, habs]

/-- `axi:stdlib/geometry/angle-construction-unique`: on one side of `AB`, two rays from
`A` making the same angle with `AB` are one ray. -/
theorem angle_construction_unique (E A B C D : ℂ) (h1 : Triangle A B C)
    (h2 : 0 < Complex.im ((D - A) / (B - A)) * Complex.im ((C - A) / (B - A)))
    (h3 : 0 < Complex.im ((E - A) / (B - A)) * Complex.im ((C - A) / (B - A)))
    (h4 : EuclideanGeometry.angle B A D = EuclideanGeometry.angle B A E) :
    E ∈ ray A D := by
  have hAB := h1.1
  have hBA : B - A ≠ 0 := sub_ne_zero.mpr hAB.symm
  have hD : Complex.im ((D - A) / (B - A)) ≠ 0 := by
    intro h; rw [h, zero_mul] at h2; exact lt_irrefl 0 h2
  have hE : Complex.im ((E - A) / (B - A)) ≠ 0 := by
    intro h; rw [h, zero_mul] at h3; exact lt_irrefl 0 h3
  have hDA : D ≠ A := by rintro rfl; simp at hD
  have hEA : E ≠ A := by rintro rfl; simp at hE
  have hzD : (D - A) / (B - A) ≠ 0 := div_ne_zero (sub_ne_zero.mpr hDA) hBA
  have hzE : (E - A) / (B - A) ≠ 0 := div_ne_zero (sub_ne_zero.mpr hEA) hBA
  rw [angle_eq_abs_signed_angle B A D hAB.symm hDA,
    angle_eq_abs_signed_angle B A E hAB.symm hEA] at h4
  have harg : Complex.arg ((D - A) / (B - A)) = Complex.arg ((E - A) / (B - A)) := by
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos h2 with ⟨d1, c1⟩ | ⟨d1, c1⟩ <;>
      rcases pos_and_pos_or_neg_and_neg_of_mul_pos h3 with ⟨e1, c2⟩ | ⟨e1, c2⟩
    · rw [abs_of_pos (arg_pos_of_im_pos d1), abs_of_pos (arg_pos_of_im_pos e1)] at h4
      exact h4
    · linarith
    · linarith
    · rw [abs_of_neg (Complex.arg_neg_iff.mpr d1), abs_of_neg (Complex.arg_neg_iff.mpr e1)] at h4
      linarith
  have hr := (Complex.arg_eq_arg_iff hzD hzE).mp harg
  have hq : (E - A) / (D - A) = ((‖(E - A) / (B - A)‖ / ‖(D - A) / (B - A)‖ : ℝ) : ℂ) := by
    have hDA' : D - A ≠ 0 := sub_ne_zero.mpr hDA
    rw [show (E - A) / (D - A) = (E - A) / (B - A) / ((D - A) / (B - A)) by field_simp,
      Complex.ofReal_div]
    conv_lhs => rw [← hr]
    field_simp
  refine ⟨hDA.symm, ?_, ?_⟩
  · rw [hq, Complex.ofReal_im]
  · rw [hq, Complex.ofReal_re]; positivity

/-- `axi:stdlib/geometry/angle-addition-inside`: a ray from `A` inside the angle `BAC`
splits it in two. -/
theorem angle_addition_inside (A B C D : ℂ) (h1 : Triangle A B C)
    (h2 : 0 < Complex.im ((D - A) / (B - A)) * Complex.im ((C - A) / (B - A)))
    (h3 : 0 < Complex.im ((D - A) / (C - A)) * Complex.im ((B - A) / (C - A))) :
    EuclideanGeometry.angle B A D + EuclideanGeometry.angle D A C =
      EuclideanGeometry.angle B A C := by
  obtain ⟨hAB, -, hAC, -⟩ := h1
  have hD : Complex.im ((D - A) / (B - A)) ≠ 0 := by
    intro h; rw [h, zero_mul] at h2; exact lt_irrefl 0 h2
  have hDA : D ≠ A := by rintro rfl; simp at hD
  have hB : B - A ≠ 0 := sub_ne_zero.mpr hAB.symm
  have hC : C - A ≠ 0 := sub_ne_zero.mpr hAC.symm
  have hD' : D - A ≠ 0 := sub_ne_zero.mpr hDA
  rw [angle_eq_abs_signed_angle B A D hAB.symm hDA, angle_eq_abs_signed_angle D A C hDA hAC.symm,
    angle_eq_abs_signed_angle B A C hAB.symm hAC.symm]
  obtain ⟨k, hk⟩ := three_rays B C A D hAB.symm hAC.symm hDA
  have e1 : Complex.im ((C - A) / (D - A)) =
      -Complex.im ((D - A) / (C - A)) / Complex.normSq ((D - A) / (C - A)) := by
    rw [← inv_div, Complex.inv_im]
  have e2 : Complex.im ((C - A) / (B - A)) =
      -Complex.im ((B - A) / (C - A)) / Complex.normSq ((B - A) / (C - A)) := by
    rw [← inv_div, Complex.inv_im]
  have n1 : 0 < Complex.normSq ((D - A) / (C - A)) := Complex.normSq_pos.mpr (div_ne_zero hD' hC)
  have n2 : 0 < Complex.normSq ((B - A) / (C - A)) := Complex.normSq_pos.mpr (div_ne_zero hB hC)
  have h3' : 0 < Complex.im ((C - A) / (D - A)) * Complex.im ((C - A) / (B - A)) := by
    rw [e1, e2, show ∀ a b n m : ℝ, -a / n * (-b / m) = a * b / (n * m) by intros; ring]
    exact div_pos h3 (mul_pos n1 n2)
  have hpi := Real.pi_pos
  have l1 := Complex.neg_pi_lt_arg ((D - A) / (B - A))
  have u1 := Complex.arg_le_pi ((D - A) / (B - A))
  have l2 := Complex.neg_pi_lt_arg ((C - A) / (D - A))
  have u2 := Complex.arg_le_pi ((C - A) / (D - A))
  have l3 := Complex.neg_pi_lt_arg ((C - A) / (B - A))
  have u3 := Complex.arg_le_pi ((C - A) / (B - A))
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos h2 with ⟨d1, c1⟩ | ⟨d1, c1⟩
  · have a1 := arg_pos_of_im_pos d1
    have a2 := arg_pos_of_im_pos (pos_of_mul_pos_left h3' c1.le)
    have a3 := arg_pos_of_im_pos c1
    have kl : (k : ℝ) < 1 := by by_contra h; rw [not_lt] at h; nlinarith
    have kg : (-1 : ℝ) < k := by by_contra h; rw [not_lt] at h; nlinarith
    have hk0 : k = 0 := by
      have : k < 1 := by exact_mod_cast kl
      have : -1 < k := by exact_mod_cast kg
      omega
    rw [hk0] at hk
    rw [abs_of_pos a1, abs_of_pos a2, abs_of_pos a3]
    push_cast at hk
    linarith
  · have a1 := Complex.arg_neg_iff.mpr d1
    have a2 := Complex.arg_neg_iff.mpr (neg_of_mul_pos_left h3' c1.le)
    have a3 := Complex.arg_neg_iff.mpr c1
    have kl : (k : ℝ) < 1 := by by_contra h; rw [not_lt] at h; nlinarith
    have kg : (-1 : ℝ) < k := by by_contra h; rw [not_lt] at h; nlinarith
    have hk0 : k = 0 := by
      have : k < 1 := by exact_mod_cast kl
      have : -1 < k := by exact_mod_cast kg
      omega
    rw [hk0] at hk
    rw [abs_of_neg a1, abs_of_neg a2, abs_of_neg a3]
    push_cast at hk
    linarith

/-- Half two sides times the size of the sine of the signed angle between them is half
the size of the cross product of the two sides. -/
theorem area_eq_abs_cross (P Q R : ℂ) :
    1 / 2 * (dist Q R * dist P R) * |Real.sin (Complex.arg ((P - R) / (Q - R)))| =
      1 / 2 * |(P - R).im * (Q - R).re - (P - R).re * (Q - R).im| := by
  rw [Complex.sin_arg]
  by_cases hQ : Q - R = 0
  · rw [Complex.dist_eq, hQ]; simp
  by_cases hP : P - R = 0
  · rw [hP]; simp
  have nq : 0 < ‖Q - R‖ := norm_pos_iff.mpr hQ
  have np : 0 < ‖P - R‖ := norm_pos_iff.mpr hP
  have him : ((P - R) / (Q - R)).im =
      ((P - R).im * (Q - R).re - (P - R).re * (Q - R).im) / ‖Q - R‖ ^ 2 := by
    rw [Complex.div_im, Complex.normSq_eq_norm_sq]; ring
  rw [him, norm_div, Complex.dist_eq, Complex.dist_eq, abs_div, abs_div,
    abs_of_pos (pow_pos nq 2), abs_of_pos (div_pos np nq)]
  field_simp

/-- `axi:stdlib/geometry/area-congruent`: congruent triangles have one area. -/
theorem area_congruent (P P' Q Q' R R' : ℂ) (h1 : Triangle P Q R) (h2 : Triangle P' Q' R')
    (h3 : dist P Q = dist P' Q' ∧ dist Q R = dist Q' R' ∧ dist R P = dist R' P' ∧
      EuclideanGeometry.angle P Q R = EuclideanGeometry.angle P' Q' R' ∧
      EuclideanGeometry.angle Q R P = EuclideanGeometry.angle Q' R' P' ∧
      EuclideanGeometry.angle R P Q = EuclideanGeometry.angle R' P' Q') :
    1 / 2 * (dist Q R * dist P R) * abs (Real.sin (Complex.arg ((P - R) / (Q - R)))) =
      1 / 2 * (dist Q' R' * dist P' R') * abs (Real.sin (Complex.arg ((P' - R') / (Q' - R')))) := by
  obtain ⟨-, hQR, hPR, -⟩ := h1
  obtain ⟨-, hQR', hPR', -⟩ := h2
  obtain ⟨-, e1, e2, -, e3, -⟩ := h3
  rw [abs_sin_arg_eq_sin_angle P Q R hPR hQR, abs_sin_arg_eq_sin_angle P' Q' R' hPR' hQR', e1,
    dist_comm P R, e2, dist_comm R' P', e3]

/-- `axi:stdlib/geometry/area-base-height`: the area is half the base times the height,
the distance from the opposite vertex to the foot of the perpendicular. -/
theorem area_base_height (H P Q R : ℂ) (_h1 : Triangle P Q R) (h2 : H ∈ line Q R)
    (h3 : P ≠ H ∧ Q ≠ R ∧ Complex.re ((R - Q) / (H - P)) = 0) :
    1 / 2 * (dist Q R * dist P R) * abs (Real.sin (Complex.arg ((P - R) / (Q - R)))) =
      1 / 2 * dist Q R * dist P H := by
  obtain ⟨hPH, hQR, hre⟩ := h3
  have hRQ : R - Q ≠ 0 := sub_ne_zero.mpr hQR.symm
  have hHP : H - P ≠ 0 := sub_ne_zero.mpr (Ne.symm hPH)
  have hH := eq_add_re_mul H Q R hRQ h2.2
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ((H - Q) / (R - Q)).re := ⟨_, rfl⟩
  rw [← ht] at hH
  have hHre : H.re = Q.re + t * (R.re - Q.re) := by
    have := congrArg Complex.re hH; simpa using this
  have hHim : H.im = Q.im + t * (R.im - Q.im) := by
    have := congrArg Complex.im hH; simpa using this
  have hn : 0 < Complex.normSq (H - P) := Complex.normSq_pos.mpr hHP
  have hdot : (R.re - Q.re) * (H.re - P.re) + (R.im - Q.im) * (H.im - P.im) = 0 := by
    rw [Complex.div_re] at hre
    simp only [Complex.sub_re, Complex.sub_im] at hre
    field_simp at hre
    linarith
  have hsq : ((P - R).im * (Q - R).re - (P - R).re * (Q - R).im) ^ 2 =
      (dist Q R * dist P H) ^ 2 := by
    rw [mul_pow, Complex.dist_eq_re_im, Complex.dist_eq_re_im, Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)]
    simp only [Complex.sub_re, Complex.sub_im]
    rw [hHre, hHim] at hdot ⊢
    linear_combination (-((R.re - Q.re) * (Q.re + t * (R.re - Q.re) - P.re) +
      (R.im - Q.im) * (Q.im + t * (R.im - Q.im) - P.im))) * hdot
  rw [area_eq_abs_cross, ← Real.sqrt_sq_eq_abs, hsq, Real.sqrt_sq (by positivity)]
  ring

/-- `axi:stdlib/geometry/area-addition`: a point strictly inside side `QR` cuts the
triangle into two whose areas add to its own. -/
theorem area_addition (D P Q R : ℂ) (_h1 : Triangle P Q R) (h2 : Sbtw ℝ Q D R) :
    1 / 2 * (dist Q R * dist P R) * abs (Real.sin (Complex.arg ((P - R) / (Q - R)))) =
      1 / 2 * (dist Q D * dist P D) * abs (Real.sin (Complex.arg ((P - D) / (Q - D)))) +
        1 / 2 * (dist D R * dist P R) * abs (Real.sin (Complex.arg ((P - R) / (D - R)))) := by
  obtain ⟨-, s, hs0, hs1, hD⟩ := (sbtw_iff_exists_real Q D R).mp h2
  rw [area_eq_abs_cross, area_eq_abs_cross, area_eq_abs_cross]
  have e1 : (P - D).im * (Q - D).re - (P - D).re * (Q - D).im =
      s * ((P - R).im * (Q - R).re - (P - R).re * (Q - R).im) := by
    rw [hD]
    simp only [Complex.sub_re, Complex.add_re, Complex.sub_im, Complex.add_im,
      Complex.re_ofReal_mul, Complex.im_ofReal_mul]
    ring
  have e2 : (P - R).im * (D - R).re - (P - R).re * (D - R).im =
      (1 - s) * ((P - R).im * (Q - R).re - (P - R).re * (Q - R).im) := by
    rw [hD]
    simp only [Complex.sub_re, Complex.add_re, Complex.sub_im, Complex.add_im,
      Complex.re_ofReal_mul, Complex.im_ofReal_mul]
    ring
  rw [e1, e2, abs_mul, abs_mul, abs_of_pos hs0, abs_of_pos (by linarith : (0 : ℝ) < 1 - s)]
  ring

/-- `mun:stdlib/geometry/segment-extension`: a segment extends beyond its end by any
positive length. -/
theorem segment_extension (A B : ℂ) (r : ℝ) (h2 : A ≠ B) (h3 : 0 < r) :
    ∃ X ∈ (Set.univ : Set ℂ), Sbtw ℝ A B X ∧ dist B X = r := by
  have hd : 0 < dist A B := dist_pos.mpr h2
  have hBA : B - A ≠ 0 := sub_ne_zero.mpr h2.symm
  have hd0 : (dist A B : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hdr : (dist A B : ℂ) + r ≠ 0 := by exact_mod_cast (by linarith : dist A B + r ≠ 0)
  refine ⟨B + ((r / dist A B : ℝ) : ℂ) * (B - A), trivial, ?_, ?_⟩
  · rw [sbtw_iff_exists_real]
    refine ⟨?_, dist A B / (dist A B + r), by positivity,
      by rw [div_lt_one (by positivity)]; linarith, ?_⟩
    · intro h
      have h0 : ((1 + r / dist A B : ℝ) : ℂ) * (B - A) = 0 := by
        push_cast at h ⊢; linear_combination -h
      rcases mul_eq_zero.mp h0 with h | h
      · have : (1 + r / dist A B : ℝ) = 0 := by exact_mod_cast h
        have : 0 < 1 + r / dist A B := by positivity
        linarith
      · exact hBA h
    · push_cast; field_simp; ring
  · rw [Complex.dist_eq, show B - (B + ((r / dist A B : ℝ) : ℂ) * (B - A)) =
      -(((r / dist A B : ℝ) : ℂ) * (B - A)) by ring, norm_neg, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity), ← Complex.dist_eq, dist_comm B A]
    field_simp

/-- `mun:stdlib/geometry/segment-point`: a segment has a point at any distance from one
end shorter than its length. -/
theorem segment_point (A B : ℂ) (r : ℝ) (h2 : 0 < r) (h3 : r < dist A B) :
    ∃ X ∈ (Set.univ : Set ℂ), Sbtw ℝ A X B ∧ dist A X = r := by
  have hd : 0 < dist A B := by linarith
  have hAB : A ≠ B := dist_pos.mp hd
  refine ⟨A + ((r / dist A B : ℝ) : ℂ) * (B - A), trivial, ?_, ?_⟩
  · rw [sbtw_iff_exists_real]
    exact ⟨hAB, _, by positivity, (div_lt_one hd).mpr h3, rfl⟩
  · rw [Complex.dist_eq, show A - (A + ((r / dist A B : ℝ) : ℂ) * (B - A)) =
      -(((r / dist A B : ℝ) : ℂ) * (B - A)) by ring, norm_neg, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity), ← Complex.dist_eq, dist_comm B A]
    field_simp

/-- `mun:stdlib/geometry/triangle-off-line`: a point off line `QR` makes a triangle
with `Q` and `R`. -/
theorem triangle_off_line (P Q R : ℂ) (h1 : Q ≠ R) (h2 : ¬ P ∈ line Q R) : Triangle P Q R := by
  have hc : ¬ Collinear ℝ ({Q, R, P} : Set ℂ) :=
    fun h => h2 ((mem_line_iff_collinear Q R P h1).mpr h)
  refine ⟨?_, h1, ?_, fun h => hc ((collinear_rot_231 P Q R).mp h)⟩
  · rintro rfl; exact h2 ⟨h1, by simp⟩
  · rintro rfl; exact h2 ⟨h1, by simp [div_self (sub_ne_zero.mpr h1.symm)]⟩

/-- `mun:stdlib/geometry/perpendicular-along`: a line perpendicular to `CD` is
perpendicular to the line through any two points of `CD`. -/
theorem perpendicular_along (A B C D E F : ℂ)
    (h1 : A ≠ B ∧ C ≠ D ∧ Complex.re ((D - C) / (B - A)) = 0) (h2 : E ∈ line C D)
    (h3 : F ∈ line C D) (h4 : E ≠ F) :
    A ≠ B ∧ E ≠ F ∧ Complex.re ((F - E) / (B - A)) = 0 := by
  obtain ⟨hAB, hCD, hre⟩ := h1
  have hDC : D - C ≠ 0 := sub_ne_zero.mpr hCD.symm
  refine ⟨hAB, h4, ?_⟩
  have e : (F - E) / (B - A) = ((((F - C) / (D - C)).re - ((E - C) / (D - C)).re : ℝ) : ℂ) *
      ((D - C) / (B - A)) := by
    conv_lhs => rw [eq_add_re_mul F C D hDC h3.2, eq_add_re_mul E C D hDC h2.2]
    push_cast; ring
  rw [e, Complex.re_ofReal_mul, hre, mul_zero]

/-- `mun:stdlib/geometry/area-rotated`: the area read from each vertex in turn is one. -/
theorem area_rotated (P Q R : ℂ) (_h1 : Triangle P Q R) :
    1 / 2 * (dist Q R * dist P R) * abs (Real.sin (Complex.arg ((P - R) / (Q - R)))) =
      1 / 2 * (dist R P * dist Q P) * abs (Real.sin (Complex.arg ((Q - P) / (R - P)))) := by
  rw [area_eq_abs_cross, area_eq_abs_cross]
  simp only [Complex.sub_re, Complex.sub_im]
  ring_nf

/-- For `C`, `D` apart on line `AB`, the quotient by `D − C` of a point's step from `C`
has the imaginary part of its quotient by `B − A`, over a real number that is not 0. -/
theorem im_ratio_on_line (A B C D : ℂ) (h1 : A ≠ B) (h2 : C ≠ D) (h3 : C ∈ line A B)
    (h4 : D ∈ line A B) :
    ∃ t : ℝ, t ≠ 0 ∧ ∀ Y : ℂ,
      Complex.im ((Y - C) / (D - C)) = Complex.im ((Y - A) / (B - A)) / t := by
  have hBA : B - A ≠ 0 := sub_ne_zero.mpr h1.symm
  have hC := eq_add_re_mul C A B hBA h3.2
  have hD := eq_add_re_mul D A B hBA h4.2
  set c := ((C - A) / (B - A)).re
  set d := ((D - A) / (B - A)).re
  have hdc : d - c ≠ 0 := by
    intro h
    apply h2
    rw [hC, hD, show d = c by linarith]
  refine ⟨d - c, hdc, fun Y => ?_⟩
  have hdc' : ((d - c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hdc
  have hDC : D - C = ((d - c : ℝ) : ℂ) * (B - A) := by rw [hD, hC]; push_cast; ring
  have hYC : Y - C = (Y - A) - (c : ℂ) * (B - A) := by rw [hC]; ring
  have e : (Y - C) / (D - C) = ((Y - A) / (B - A) - c) / ((d - c : ℝ) : ℂ) := by
    rw [hDC, hYC]; field_simp
  rw [e, Complex.div_ofReal_im, Complex.sub_im, Complex.ofReal_im, sub_zero]

/-- `mun:stdlib/geometry/same-side-of-line`: which side a point is on belongs to the
line, not to the two points that name it. -/
theorem same_side_of_line (A B C D P Q : ℂ) (h1 : A ≠ B) (h2 : C ≠ D)
    (h3 : C ∈ line A B) (h4 : D ∈ line A B)
    (h5 : 0 < Complex.im ((P - A) / (B - A)) * Complex.im ((Q - A) / (B - A))) :
    0 < Complex.im ((P - C) / (D - C)) * Complex.im ((Q - C) / (D - C)) := by
  obtain ⟨t, ht, e⟩ := im_ratio_on_line A B C D h1 h2 h3 h4
  rw [e P, e Q, div_mul_div_comm]
  exact div_pos h5 (mul_self_pos.mpr ht)

/-- `mun:stdlib/geometry/opposite-sides-of-line`: which side a point is on belongs to
the line, not to the two points that name it. -/
theorem opposite_sides_of_line (A B C D P Q : ℂ) (h1 : A ≠ B) (h2 : C ≠ D)
    (h3 : C ∈ line A B) (h4 : D ∈ line A B)
    (h5 : Complex.im ((P - A) / (B - A)) * Complex.im ((Q - A) / (B - A)) < 0) :
    Complex.im ((P - C) / (D - C)) * Complex.im ((Q - C) / (D - C)) < 0 := by
  obtain ⟨t, ht, e⟩ := im_ratio_on_line A B C D h1 h2 h3 h4
  rw [e P, e Q, div_mul_div_comm]
  exact div_neg_of_neg_of_pos h5 (mul_self_pos.mpr ht)

/-- `mun:stdlib/geometry/segment-off-line`: a segment from a point off a line to a
point on it stays on the first point's side. -/
theorem segment_off_line (A B P Q X : ℂ) (h1 : A ≠ B) (h2 : Q ∈ line A B)
    (h3 : ¬ P ∈ line A B) (h4 : Sbtw ℝ P X Q) :
    0 < Complex.im ((X - A) / (B - A)) * Complex.im ((P - A) / (B - A)) := by
  obtain ⟨-, s, hs0, hs1, hX⟩ := (sbtw_iff_exists_real P X Q).mp h4
  have hBA : B - A ≠ 0 := sub_ne_zero.mpr h1.symm
  have hp : Complex.im ((P - A) / (B - A)) ≠ 0 := fun h => h3 ⟨h1, h⟩
  rw [ratio_along A B P Q X s hBA hX, Complex.add_im, Complex.im_ofReal_mul, Complex.sub_im,
    h2.2]
  have hp2 : 0 < Complex.im ((P - A) / (B - A)) ^ 2 := by positivity
  nlinarith [mul_pos (sub_pos.mpr hs1) hp2]

/-- `mun:stdlib/geometry/segment-across-line`: a segment through a point of a line,
from a point off it, ends on the other side. -/
theorem segment_across_line (A B M P Q : ℂ) (h1 : A ≠ B) (h2 : M ∈ line A B)
    (h3 : ¬ P ∈ line A B) (h4 : Sbtw ℝ P M Q) :
    Complex.im ((P - A) / (B - A)) * Complex.im ((Q - A) / (B - A)) < 0 := by
  obtain ⟨-, s, hs0, hs1, hM⟩ := (sbtw_iff_exists_real P M Q).mp h4
  have hBA : B - A ≠ 0 := sub_ne_zero.mpr h1.symm
  have hp : Complex.im ((P - A) / (B - A)) ≠ 0 := fun h => h3 ⟨h1, h⟩
  have hm := h2.2
  rw [ratio_along A B P Q M s hBA hM, Complex.add_im, Complex.im_ofReal_mul,
    Complex.sub_im] at hm
  have hp2 : 0 < Complex.im ((P - A) / (B - A)) ^ 2 := by positivity
  have key : s * (Complex.im ((P - A) / (B - A)) * Complex.im ((Q - A) / (B - A))) =
      -((1 - s) * Complex.im ((P - A) / (B - A)) ^ 2) := by
    linear_combination Complex.im ((P - A) / (B - A)) * hm
  have : 0 < (1 - s) * Complex.im ((P - A) / (B - A)) ^ 2 := mul_pos (by linarith) hp2
  nlinarith

/-- `mun:stdlib/geometry/segment-beyond-off-line`: a segment from a point of a line
through a point off it goes on, past that point, on its side. -/
theorem segment_beyond_off_line (A B P Q X : ℂ) (h1 : A ≠ B) (h2 : Q ∈ line A B)
    (h3 : ¬ X ∈ line A B) (h4 : Sbtw ℝ P X Q) :
    0 < Complex.im ((P - A) / (B - A)) * Complex.im ((X - A) / (B - A)) := by
  obtain ⟨-, s, hs0, hs1, hX⟩ := (sbtw_iff_exists_real P X Q).mp h4
  have hBA : B - A ≠ 0 := sub_ne_zero.mpr h1.symm
  have hx : Complex.im ((X - A) / (B - A)) ≠ 0 := fun h => h3 ⟨h1, h⟩
  rw [ratio_along A B P Q X s hBA hX, Complex.add_im, Complex.im_ofReal_mul, Complex.sub_im,
    h2.2] at hx ⊢
  have hp : Complex.im ((P - A) / (B - A)) ≠ 0 := by
    intro h; rw [h] at hx; simp at hx
  have hp2 : 0 < Complex.im ((P - A) / (B - A)) ^ 2 := by positivity
  nlinarith [mul_pos (sub_pos.mpr hs1) hp2]

/-- `mun:stdlib/geometry/triangle-extension`: a side produced past a vertex makes a
triangle with the third vertex. -/
theorem triangle_extension (P Q R S : ℂ) (h1 : Triangle P Q R) (h2 : Sbtw ℝ R Q S) :
    Triangle P Q S := by
  obtain ⟨hPQ, -, -, hcol⟩ := h1
  have hc : Collinear ℝ ({Q, S, R} : Set ℂ) := by
    have := h2.wbtw.collinear
    exact (collinear_rot_231 R Q S).mp this
  refine ⟨hPQ, h2.ne_right, ?_, fun h => hcol ?_⟩
  · rintro rfl
    exact hcol ((collinear_swap_12 P Q R).mpr hc)
  · have h' : Collinear ℝ (insert P ({Q, S, R} : Set ℂ)) :=
      (hc.collinear_insert_iff_of_ne (by simp) (by simp) h2.ne_right).mpr h
    exact h'.subset (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto)

/-- `mun:stdlib/geometry/off-line-through`: two lines through `R` meet only at `R`. -/
theorem off_line_through (P R S X : ℂ) (h1 : ¬ S ∈ line R P) (h2 : X ∈ line R S)
    (h3 : X ≠ R) : ¬ X ∈ line R P := by
  rintro ⟨hRP, hX⟩
  have hSR : S - R ≠ 0 := sub_ne_zero.mpr h2.1.symm
  have hPR : P - R ≠ 0 := sub_ne_zero.mpr hRP.symm
  have e := eq_add_re_mul X R S hSR h2.2
  set x := ((X - R) / (S - R)).re
  have hx : x ≠ 0 := by
    intro h0; apply h3; rw [e, h0]; simp
  have : (X - R) / (P - R) = (x : ℂ) * ((S - R) / (P - R)) := by
    rw [e]; field_simp; ring
  rw [this, Complex.im_ofReal_mul] at hX
  exact h1 ⟨hRP, (mul_eq_zero.mp hX).resolve_left hx⟩

/-- `mun:stdlib/geometry/line-crossing-between`: a point of a line through `R` on the
far side of another line through `R` is beyond `R`. -/
theorem line_crossing_between (P R S X : ℂ) (h1 : X ∈ line R S)
    (h2 : Complex.im ((S - R) / (P - R)) * Complex.im ((X - R) / (P - R)) < 0) :
    Sbtw ℝ S R X := by
  have hSR : S - R ≠ 0 := sub_ne_zero.mpr h1.1.symm
  have e := eq_add_re_mul X R S hSR h1.2
  set x := ((X - R) / (S - R)).re
  have hq : (X - R) / (P - R) = (x : ℂ) * ((S - R) / (P - R)) := by
    rw [e]; ring
  rw [hq, Complex.im_ofReal_mul] at h2
  have hx : x < 0 := by
    by_contra h
    nlinarith [mul_nonneg (not_lt.mp h) (sq_nonneg (Complex.im ((S - R) / (P - R))))]
  rw [sbtw_iff_exists_real]
  have h1x : (1 : ℂ) - x ≠ 0 := by
    intro h
    have : (x : ℂ) = 1 := by linear_combination -h
    have : x = 1 := by exact_mod_cast this
    linarith
  refine ⟨fun hSX => ?_, 1 / (1 - x), by apply div_pos <;> linarith,
    by rw [div_lt_one (by linarith)]; linarith, ?_⟩
  · rw [← hSX] at e
    have : ((1 : ℂ) - x) * (S - R) = 0 := by linear_combination e
    rcases mul_eq_zero.mp this with h | h
    · exact h1x h
    · exact hSR h
  · rw [e]; push_cast; field_simp; ring

/-- `mun:stdlib/geometry/angle-same-ray`: a point of line `PQ` on `Q`'s side of line
`PR` is on the ray from `P` through `Q`, so it makes the same angle. -/
theorem angle_same_ray (P Q R X : ℂ) (h1 : X ∈ line P Q)
    (h2 : 0 < Complex.im ((X - P) / (R - P)) * Complex.im ((Q - P) / (R - P))) :
    EuclideanGeometry.angle R P X = EuclideanGeometry.angle R P Q := by
  have hQP : Q - P ≠ 0 := sub_ne_zero.mpr h1.1.symm
  have e := eq_add_re_mul X P Q hQP h1.2
  set x := ((X - P) / (Q - P)).re
  have hq : (X - P) / (R - P) = (x : ℂ) * ((Q - P) / (R - P)) := by
    rw [e]; ring
  rw [hq, Complex.im_ofReal_mul] at h2
  have hx : 0 < x := by
    by_contra h
    nlinarith [mul_nonneg (neg_nonneg.mpr (not_lt.mp h)) (sq_nonneg (Complex.im ((Q - P) / (R - P))))]
  unfold EuclideanGeometry.angle
  have : X -ᵥ P = x • (Q -ᵥ P) := by
    rw [vsub_eq_sub, vsub_eq_sub, Complex.real_smul, e]; ring
  rw [this, InnerProductGeometry.angle_smul_right_of_pos _ _ hx]

/-- `mun:stdlib/geometry/parallel-along`: being parallel belongs to the two lines, not
to the points that name them. -/
theorem parallel_along (A B C D E : ℂ) (h1 : Complex.im ((B - A) / (D - C)) = 0)
    (h2 : A ≠ B) (h3 : E ∈ line A B) (_h4 : E ≠ A) :
    Complex.im ((E - A) / (C - D)) = 0 := by
  have e : (E - A) / (C - D) = -(((E - A) / (B - A)).re : ℂ) * ((B - A) / (D - C)) := by
    conv_lhs => rw [eq_add_re_mul E A B (sub_ne_zero.mpr h2.symm) h3.2]
    rw [show C - D = -(D - C) by ring, div_neg]
    ring
  rw [e, neg_mul, Complex.neg_im, Complex.im_ofReal_mul, h1, mul_zero, neg_zero]

/-- `mun:stdlib/geometry/ray-side-transfer`: a point on the ray from `R` through `P`
is on `P`'s side of every line through `R` that `P` is off. -/
theorem ray_side_transfer (P Q R S X : ℂ) (h1 : X ∈ line R P)
    (h2 : 0 < Complex.im ((X - R) / (S - R)) * Complex.im ((P - R) / (S - R)))
    (h3 : R ≠ Q) (h4 : ¬ P ∈ line R Q) :
    0 < Complex.im ((X - R) / (Q - R)) * Complex.im ((P - R) / (Q - R)) := by
  have hX := eq_add_re_mul X R P (sub_ne_zero.mpr h1.1.symm) h1.2
  set t := ((X - R) / (P - R)).re
  have hXR : X - R = (t : ℂ) * (P - R) := by rw [hX]; ring
  have hb : Complex.im ((P - R) / (Q - R)) ≠ 0 := fun h => h4 ⟨h3, h⟩
  rw [hXR, mul_div_assoc, Complex.im_ofReal_mul] at h2 ⊢
  have ht : 0 < t := by
    by_contra hn
    push Not at hn
    nlinarith [mul_self_nonneg (Complex.im ((P - R) / (S - R)))]
  have := mul_self_pos.mpr hb
  nlinarith

end LeanBridges.Geometry
