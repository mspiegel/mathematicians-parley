module

public import Tactics

/-! Written from corpus/stdlib/trigonometry.records by parley build lean. -/

public section

namespace Parley.Items.Stdlib.Trigonometry

theorem thm_cos_add (a : ℂ) (b : ℂ) :
    Complex.cos (a + b) = Complex.cos a * Complex.cos b - Complex.sin a * Complex.sin b :=
  Complex.cos_add a b

theorem thm_sin_add (a : ℂ) (b : ℂ) :
    Complex.sin (a + b) = Complex.sin a * Complex.cos b + Complex.cos a * Complex.sin b :=
  Complex.sin_add a b

theorem mun_cos_zero :
    Real.cos (0 : ℝ) = 1 :=
  by (simp_all; done)

theorem mun_sin_zero :
    Real.sin (0 : ℝ) = 0 :=
  by (simp_all; done)

theorem mun_cos_real (a : ℝ) :
    True :=
  by (simp_all; done)

theorem mun_cos_complex (a : ℂ) :
    True :=
  trivial

theorem mun_sin_complex (a : ℂ) :
    True :=
  trivial

theorem mun_cos_negative (a : ℂ) :
    Complex.cos (-a) = Complex.cos a :=
  Complex.cos_neg a

theorem mun_sin_negative (a : ℂ) :
    Complex.sin (-a) = -Complex.sin a :=
  Complex.sin_neg a

theorem mun_sin_cos_squares (a : ℂ) :
    Complex.sin a ^ 2 + Complex.cos a ^ 2 = 1 :=
  Complex.sin_sq_add_cos_sq a

theorem mun_sin_nonneg (a : ℝ) (h1 : a ∈ (Set.Icc (0 : ℝ) Real.pi : Set ℝ)) :
    0 ≤ Real.sin a :=
  Real.sin_nonneg_of_nonneg_of_le_pi h1.1 h1.2

theorem mun_sin_positive (a : ℝ) (h1 : a ∈ (Set.Ioo (0 : ℝ) Real.pi : Set ℝ)) :
    0 < Real.sin a :=
  Real.sin_pos_of_pos_of_lt_pi h1.1 h1.2

theorem mun_cos_nonneg (a : ℝ) (h1 : a ∈ (Set.Icc (-(Real.pi / 2)) (Real.pi / 2) : Set ℝ)) :
    0 ≤ Real.cos a :=
  Real.cos_nonneg_of_mem_Icc h1

theorem mun_cos_positive (a : ℝ) (h1 : a ∈ (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) : Set ℝ)) :
    0 < Real.cos a :=
  Real.cos_pos_of_mem_Ioo h1

theorem mun_sin_bounded_1 (a : ℝ) :
    -1 ≤ Real.sin a :=
  Real.neg_one_le_sin a

theorem mun_sin_bounded_2 (a : ℝ) :
    Real.sin a ≤ 1 :=
  Real.sin_le_one a

theorem mun_cos_bounded_1 (a : ℝ) :
    -1 ≤ Real.cos a :=
  Real.neg_one_le_cos a

theorem mun_cos_bounded_2 (a : ℝ) :
    Real.cos a ≤ 1 :=
  Real.cos_le_one a

theorem mun_cos_decreasing (a : ℝ) (b : ℝ) (h1 : a ∈ (Set.Icc (0 : ℝ) Real.pi : Set ℝ)) (h2 : b ∈ (Set.Icc (0 : ℝ) Real.pi : Set ℝ)) :
    a < b ↔ Real.cos b < Real.cos a :=
  ⟨fun h => Real.cos_lt_cos_of_nonneg_of_le_pi h1.1 h2.2 h, fun h => by by_contra hle; push_neg at hle; have h' := Real.cos_le_cos_of_nonneg_of_le_pi h2.1 h1.2 hle; linarith⟩

theorem mun_pi_positive :
    0 < Real.pi :=
  by positivity

theorem mun_arctan_values_1 :
    Real.arctan (0 : ℝ) = 0 :=
  by (simp_all; done)

theorem mun_arctan_values_2 :
    Real.arctan (1 : ℝ) = Real.pi / 4 :=
  by (simp_all; done)

theorem mun_arctan_real (x : ℝ) :
    True :=
  by (simp_all; done)

theorem thm_continuous_arctan (g : ℝ → ℝ) (D : Set ℝ) (h1 : D ⊆ (Set.univ : Set ℝ)) (h2 : ∀ x ∈ D, g x = Real.arctan x) (hg : Set.MapsTo g D (Set.univ : Set ℝ)) :
    ContinuousOn g D :=
  Real.continuous_arctan.continuousOn.congr (fun x hx => h2 x hx)

theorem thm_derivative_arctan_1 (g : ℝ → ℝ) (D : Set ℝ) (U : Set ℝ) (h1 : D ⊆ (Set.univ : Set ℝ)) (h2 : U ⊆ D) (h3 : IsOpen U) (h4 : ∀ x ∈ D, g x = Real.arctan x) (hg : Set.MapsTo g D (Set.univ : Set ℝ)) :
    ∀ x ∈ U, D ∈ nhds x ∧ DifferentiableAt ℝ g x :=
  fun x hx => ⟨Filter.mem_of_superset (h3.mem_nhds hx) h2, (Real.differentiable_arctan x).congr_of_eventuallyEq (Filter.eventually_of_mem (Filter.mem_of_superset (h3.mem_nhds hx) h2) (fun y hy => h4 y hy))⟩

theorem thm_derivative_arctan_2 (g : ℝ → ℝ) (D : Set ℝ) (U : Set ℝ) (h1 : D ⊆ (Set.univ : Set ℝ)) (h2 : U ⊆ D) (h3 : IsOpen U) (h4 : ∀ x ∈ D, g x = Real.arctan x) (hg : Set.MapsTo g D (Set.univ : Set ℝ)) :
    ∀ x ∈ U, (deriv g) x = 1 / (1 + x ^ 2) :=
  fun x hx => by rw [Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (Filter.mem_of_superset (h3.mem_nhds hx) h2) (fun y hy => h4 y hy)), Real.deriv_arctan]

end Parley.Items.Stdlib.Trigonometry
