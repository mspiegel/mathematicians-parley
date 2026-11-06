module

public import Calculus
public import Tactics

/-! Written from corpus/stdlib/calculus.records by parley build lean. -/

public section

namespace Parley.Items.Stdlib.Calculus

theorem def_interval (x : ℝ) (a : ℝ) (b : ℝ) :
    x ∈ (Set.Icc a b : Set ℝ) ↔ (True ∧ a ≤ x) ∧ x ≤ b :=
  by simp [Set.mem_Icc]

theorem def_open_interval (x : ℝ) (a : ℝ) (b : ℝ) :
    x ∈ (Set.Ioo a b : Set ℝ) ↔ (True ∧ a < x) ∧ x < b :=
  by (simp_all; done)

theorem mun_interval_real (a : ℝ) (b : ℝ) :
    (Set.Icc a b : Set ℝ) ⊆ (Set.univ : Set ℝ) :=
  Set.subset_univ _

theorem mun_open_interval_real (a : ℝ) (b : ℝ) :
    (Set.Ioo a b : Set ℝ) ⊆ (Set.univ : Set ℝ) :=
  by (simp_all; done)

theorem mun_open_within_closed (a : ℝ) (b : ℝ) :
    (Set.Ioo a b : Set ℝ) ⊆ (Set.Icc a b : Set ℝ) :=
  Set.Ioo_subset_Icc_self

theorem mun_closed_within_open (p : ℝ) (q : ℝ) (a : ℝ) (b : ℝ) (h3 : p ∈ (Set.Ioo a b : Set ℝ)) (h4 : q ∈ (Set.Ioo a b : Set ℝ)) :
    (Set.Icc p q : Set ℝ) ⊆ (Set.Ioo a b : Set ℝ) :=
  Set.Icc_subset_Ioo h3.1 h4.2

theorem mun_open_interval_open (a : ℝ) (b : ℝ) :
    IsOpen (Set.Ioo a b : Set ℝ) :=
  isOpen_Ioo

theorem mun_open_without_point (U : Set ℝ) (c : ℝ) (h1 : U ⊆ (Set.univ : Set ℝ)) (h2 : IsOpen U) (h3 : c ∈ U) :
    IsOpen (U \ ({c} : Set ℝ)) :=
  h2.sdiff isClosed_singleton

theorem mun_reals_open :
    IsOpen (Set.univ : Set ℝ) :=
  by (simp_all; done)

theorem def_continuous_on (f : ℝ → ℝ) (D : Set ℝ) (h1 : D ⊆ (Set.univ : Set ℝ)) :
    ContinuousOn f D ↔ (∀ c ∈ D, ∀ ε : ℝ, 0 < ε → (∃ δ : ℝ, 0 < δ ∧ (∀ x ∈ D, abs (x - c) < δ → abs (f x - f c) < ε))) :=
  LeanBridges.Calculus.continuous_on f D h1

theorem def_limit_at (f : ℝ → ℝ) (D : Set ℝ) (h1 : D ⊆ (Set.univ : Set ℝ)) (c : ℝ) (L : ℝ) :
    Filter.Tendsto f (nhdsWithin c (D \ {c})) (nhds L) ↔ (∀ ε : ℝ, 0 < ε → (∃ δ : ℝ, 0 < δ ∧ (∀ x ∈ D, x ≠ c ∧ abs (x - c) < δ → abs (f x - L) < ε))) :=
  LeanBridges.Calculus.limit_at f D h1 c L

theorem def_tends_to (x : ℤ → ℝ) (L : ℝ) :
    Filter.Tendsto (fun n : ℤ => (x n : ℝ)) Filter.atTop (nhds L) ↔ (∀ ε : ℝ, 0 < ε → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → N ≤ n → abs (x n - L) < ε))) :=
  LeanBridges.Calculus.tends_to x L

theorem def_series_sum (t : ℤ → ℝ) (L : ℝ) (h2 : Filter.Tendsto (fun n : ℤ => (∑ k ∈ Finset.Icc (1 : ℤ) n, (t k : ℝ) : ℝ)) Filter.atTop (nhds L)) :
    Filter.limUnder Filter.atTop (fun n : ℤ => ∑ k ∈ Finset.Icc (1 : ℤ) n, (t k : ℝ)) = L :=
  LeanBridges.Calculus.series_sum t L h2

theorem def_series_sum_from_zero (t : ℤ → ℝ) (L : ℝ) (h2 : Filter.Tendsto (fun n : ℤ => (∑ k ∈ Finset.Icc (0 : ℤ) n, (t k : ℝ) : ℝ)) Filter.atTop (nhds L)) :
    Filter.limUnder Filter.atTop (fun n : ℤ => ∑ k ∈ Finset.Icc (0 : ℤ) n, (t k : ℝ)) = L :=
  LeanBridges.Calculus.series_sum_from_zero t L h2

theorem axi_completeness (S : Set ℝ) (h1 : S ⊆ (Set.univ : Set ℝ)) (h2 : ∃ s ∈ S, True) (h3 : ∃ u : ℝ, ∀ s ∈ S, s ≤ u) :
    ∃ c : ℝ, (∀ s ∈ S, s ≤ c) ∧ (∀ u : ℝ, (∀ s ∈ S, s ≤ u) → c ≤ u) :=
  by obtain ⟨s, hs, -⟩ := h2; obtain ⟨u, hu⟩ := h3; exact ⟨sSup S, fun x hx => le_csSup ⟨u, fun y hy => hu y hy⟩ hx, fun v hv => csSup_le ⟨s, hs⟩ (fun y hy => hv y hy)⟩

theorem thm_rolle (f : ℝ → ℝ) (a : ℝ) (b : ℝ) (h3 : a < b) (h4 : ContinuousOn f (Set.Icc a b : Set ℝ)) (h5 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (Set.Icc a b : Set ℝ) ∈ nhds x ∧ DifferentiableAt ℝ f x) (h6 : f a = f b) :
    ∃ c ∈ (Set.Ioo a b : Set ℝ), (deriv f) c = 0 :=
  exists_deriv_eq_zero h3 h4 h6

theorem thm_rolle_on_part (f : ℝ → ℝ) (D : Set ℝ) (h1 : D ⊆ (Set.univ : Set ℝ)) (a : ℝ) (b : ℝ) (h4 : a < b) (h5 : (Set.Icc a b : Set ℝ) ⊆ D) (h6 : ContinuousOn f (Set.Icc a b : Set ℝ)) (h7 : ∀ x ∈ (Set.Ioo a b : Set ℝ), D ∈ nhds x ∧ DifferentiableAt ℝ f x) (h8 : f a = f b) :
    ∃ c ∈ (Set.Ioo a b : Set ℝ), (deriv f) c = 0 :=
  exists_deriv_eq_zero h4 h6 h8

theorem mun_derivative_real (f : ℝ → ℝ) (x : ℝ) (a : ℝ) (b : ℝ) (h3 : ∀ y ∈ (Set.Ioo a b : Set ℝ), (Set.Icc a b : Set ℝ) ∈ nhds y ∧ DifferentiableAt ℝ f y) (h4 : x ∈ (Set.Ioo a b : Set ℝ)) :
    True :=
  by (simp_all; done)

theorem mun_derivative_real_on (f : ℝ → ℝ) (D : Set ℝ) (U : Set ℝ) (x : ℝ) (h1 : D ⊆ (Set.univ : Set ℝ)) (h2 : U ⊆ D) (h3 : ∀ y ∈ U, D ∈ nhds y ∧ DifferentiableAt ℝ f y) (h4 : x ∈ U) :
    True :=
  by (simp_all; done)

theorem thm_continuous_sum (F : ℝ → ℝ) (f : ℝ → ℝ) (g : ℝ → ℝ) (D : Set ℝ) (h1 : D ⊆ (Set.univ : Set ℝ)) (h2 : ∀ x ∈ D, F x = f x + g x) (h3 : ContinuousOn f D) (h4 : ContinuousOn g D) :
    ContinuousOn F D :=
  (h3.add h4).congr (fun x hx => h2 x hx)

theorem thm_continuous_difference (F : ℝ → ℝ) (f : ℝ → ℝ) (g : ℝ → ℝ) (D : Set ℝ) (h1 : D ⊆ (Set.univ : Set ℝ)) (h2 : ∀ x ∈ D, F x = f x - g x) (h3 : ContinuousOn f D) (h4 : ContinuousOn g D) :
    ContinuousOn F D :=
  (h3.sub h4).congr (fun x hx => h2 x hx)

theorem thm_continuous_linear (g : ℝ → ℝ) (D : Set ℝ) (h1 : D ⊆ (Set.univ : Set ℝ)) (m : ℝ) (h3 : ∀ x ∈ D, g x = m * x) :
    ContinuousOn g D :=
  (show Continuous fun x : ℝ => m * x by fun_prop).continuousOn.congr (fun x hx => h3 x hx)

theorem thm_continuous_square (g : ℝ → ℝ) (D : Set ℝ) (h1 : D ⊆ (Set.univ : Set ℝ)) (h2 : ∀ x ∈ D, g x = x ^ 2) :
    ContinuousOn g D :=
  (show Continuous fun x : ℝ => x ^ 2 by fun_prop).continuousOn.congr (fun x hx => h2 x hx)

theorem thm_continuous_constant (g : ℝ → ℝ) (D : Set ℝ) (h1 : D ⊆ (Set.univ : Set ℝ)) (c : ℝ) (h3 : ∀ x ∈ D, g x = c) :
    ContinuousOn g D :=
  (show Continuous fun _ : ℝ => c by fun_prop).continuousOn.congr (fun x hx => h3 x hx)

theorem thm_continuous_power (g : ℝ → ℝ) (D : Set ℝ) (h1 : D ⊆ (Set.univ : Set ℝ)) (n : ℤ) (h2 : 0 ≤ n) (h3 : ∀ x ∈ D, g x = x ^ n.toNat) :
    ContinuousOn g D :=
  (show Continuous fun x : ℝ => x ^ n.toNat by fun_prop).continuousOn.congr (fun x hx => h3 x hx)

theorem thm_continuous_scaled (F : ℝ → ℝ) (f : ℝ → ℝ) (D : Set ℝ) (h1 : D ⊆ (Set.univ : Set ℝ)) (c : ℝ) (h3 : ∀ x ∈ D, F x = c * f x) (h4 : ContinuousOn f D) :
    ContinuousOn F D :=
  (continuousOn_const.mul h4).congr (fun x hx => h3 x hx)

theorem thm_continuous_quotient (F : ℝ → ℝ) (f : ℝ → ℝ) (g : ℝ → ℝ) (D : Set ℝ) (h1 : D ⊆ (Set.univ : Set ℝ)) (h2 : ∀ x ∈ D, g x ≠ 0) (h3 : ∀ x ∈ D, F x = f x / g x) (h4 : ContinuousOn f D) (h5 : ContinuousOn g D) :
    ContinuousOn F D :=
  (h4.div h5 h2).congr (fun x hx => h3 x hx)

theorem mun_continuous_on_part (f : ℝ → ℝ) (D : Set ℝ) (S : Set ℝ) (h1 : D ⊆ (Set.univ : Set ℝ)) (h2 : S ⊆ D) (h3 : ContinuousOn f D) :
    ContinuousOn f S :=
  ContinuousOn.congr_mono h3 (fun ⦃x⦄ => congrFun rfl) h2

theorem thm_continuous_bounded (f : ℝ → ℝ) (a : ℝ) (b : ℝ) (h3 : ContinuousOn f (Set.Icc a b : Set ℝ)) :
    ∃ M : ℝ, ∀ x ∈ (Set.Icc a b : Set ℝ), abs (f x) ≤ M :=
  by obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn h3; exact ⟨M, fun x hx => by simpa [Real.norm_eq_abs] using hM x hx⟩

theorem mun_differentiable_on_part (f : ℝ → ℝ) (D : Set ℝ) (U : Set ℝ) (S : Set ℝ) (h1 : D ⊆ (Set.univ : Set ℝ)) (h2 : U ⊆ D) (h3 : S ⊆ U) (h4 : ∀ x ∈ U, D ∈ nhds x ∧ DifferentiableAt ℝ f x) :
    ∀ x ∈ S, D ∈ nhds x ∧ DifferentiableAt ℝ f x :=
  fun x hx => h4 x (h3 hx)

theorem mun_derivative_local_1 (f : ℝ → ℝ) (F : ℝ → ℝ) (D : Set ℝ) (E : Set ℝ) (U : Set ℝ) (h1 : D ⊆ (Set.univ : Set ℝ)) (h2 : E ⊆ (Set.univ : Set ℝ)) (h3 : U ⊆ D) (h4 : U ⊆ E) (h5 : IsOpen U) (h6 : ∀ x ∈ U, F x = f x) (h7 : ∀ x ∈ U, D ∈ nhds x ∧ DifferentiableAt ℝ f x) :
    ∀ x ∈ U, E ∈ nhds x ∧ DifferentiableAt ℝ F x :=
  fun x hx => ⟨Filter.mem_of_superset (h5.mem_nhds hx) h4, (h7 x hx).2.congr_of_eventuallyEq (Filter.eventually_of_mem (h5.mem_nhds hx) (fun y hy => h6 y hy))⟩

theorem mun_derivative_local_2 (f : ℝ → ℝ) (F : ℝ → ℝ) (D : Set ℝ) (E : Set ℝ) (U : Set ℝ) (h1 : D ⊆ (Set.univ : Set ℝ)) (h2 : E ⊆ (Set.univ : Set ℝ)) (h3 : U ⊆ D) (h4 : U ⊆ E) (h5 : IsOpen U) (h6 : ∀ x ∈ U, F x = f x) (h7 : ∀ x ∈ U, D ∈ nhds x ∧ DifferentiableAt ℝ f x) :
    ∀ x ∈ U, (deriv F) x = (deriv f) x :=
  fun x hx => Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (h5.mem_nhds hx) (fun y hy => h6 y hy))

theorem thm_continuous_extension (f : ℝ → ℝ) (F : ℝ → ℝ) (U : Set ℝ) (c : ℝ) (h1 : U ⊆ (Set.univ : Set ℝ)) (h2 : IsOpen U) (h3 : c ∈ U) (L : ℝ) (h5 : ∀ x ∈ U \ ({c} : Set ℝ), F x = f x) (h6 : F c = L) (h7 : ∀ x ∈ (U \ ({c} : Set ℝ)), (U \ ({c} : Set ℝ)) ∈ nhds x ∧ DifferentiableAt ℝ f x) (h8 : Filter.Tendsto f (nhdsWithin c ((U \ ({c} : Set ℝ)) \ {c})) (nhds L)) :
    ContinuousOn F U :=
  by intro x hx; by_cases hxc : x = c; (subst hxc; rw [← continuousWithinAt_sdiff_self, ContinuousWithinAt, h6]; rw [(show (U \ ({x} : Set ℝ)) \ {x} = U \ {x} by ext y; simp)] at h8; exact h8.congr' (eventually_nhdsWithin_of_forall (fun y hy => (h5 y hy).symm))); have hmem : x ∈ U \ ({c} : Set ℝ) := ⟨hx, hxc⟩; exact (((h7 x hmem).2.continuousAt).congr (Filter.eventually_of_mem ((h2.sdiff isClosed_singleton).mem_nhds hmem) (fun y hy => (h5 y hy).symm))).continuousWithinAt

theorem thm_derivative_sum_1 (F : ℝ → ℝ) (f : ℝ → ℝ) (g : ℝ → ℝ) (D : Set ℝ) (U : Set ℝ) (h1 : D ⊆ (Set.univ : Set ℝ)) (h2 : U ⊆ D) (h3 : ∀ x ∈ D, F x = f x + g x) (h4 : ∀ x ∈ U, D ∈ nhds x ∧ DifferentiableAt ℝ f x) (h5 : ∀ x ∈ U, D ∈ nhds x ∧ DifferentiableAt ℝ g x) :
    ∀ x ∈ U, D ∈ nhds x ∧ DifferentiableAt ℝ F x :=
  fun x hx => ⟨(h4 x hx).1, ((h4 x hx).2.add (h5 x hx).2).congr_of_eventuallyEq (Filter.eventually_of_mem (h4 x hx).1 (fun y hy => h3 y hy))⟩

theorem thm_derivative_sum_2 (F : ℝ → ℝ) (f : ℝ → ℝ) (g : ℝ → ℝ) (D : Set ℝ) (U : Set ℝ) (h1 : D ⊆ (Set.univ : Set ℝ)) (h2 : U ⊆ D) (h3 : ∀ x ∈ D, F x = f x + g x) (h4 : ∀ x ∈ U, D ∈ nhds x ∧ DifferentiableAt ℝ f x) (h5 : ∀ x ∈ U, D ∈ nhds x ∧ DifferentiableAt ℝ g x) :
    ∀ x ∈ U, (deriv F) x = (deriv f) x + (deriv g) x :=
  fun x hx => by rw [Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (h4 x hx).1 (fun y hy => h3 y hy))]; exact deriv_add (h4 x hx).2 (h5 x hx).2

theorem thm_derivative_difference_1 (F : ℝ → ℝ) (f : ℝ → ℝ) (g : ℝ → ℝ) (D : Set ℝ) (U : Set ℝ) (h1 : D ⊆ (Set.univ : Set ℝ)) (h2 : U ⊆ D) (h3 : ∀ x ∈ D, F x = f x - g x) (h4 : ∀ x ∈ U, D ∈ nhds x ∧ DifferentiableAt ℝ f x) (h5 : ∀ x ∈ U, D ∈ nhds x ∧ DifferentiableAt ℝ g x) :
    ∀ x ∈ U, D ∈ nhds x ∧ DifferentiableAt ℝ F x :=
  fun x hx => ⟨(h4 x hx).1, ((h4 x hx).2.sub (h5 x hx).2).congr_of_eventuallyEq (Filter.eventually_of_mem (h4 x hx).1 (fun y hy => h3 y hy))⟩

theorem thm_derivative_difference_2 (F : ℝ → ℝ) (f : ℝ → ℝ) (g : ℝ → ℝ) (D : Set ℝ) (U : Set ℝ) (h1 : D ⊆ (Set.univ : Set ℝ)) (h2 : U ⊆ D) (h3 : ∀ x ∈ D, F x = f x - g x) (h4 : ∀ x ∈ U, D ∈ nhds x ∧ DifferentiableAt ℝ f x) (h5 : ∀ x ∈ U, D ∈ nhds x ∧ DifferentiableAt ℝ g x) :
    ∀ x ∈ U, (deriv F) x = (deriv f) x - (deriv g) x :=
  fun x hx => by rw [Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (h4 x hx).1 (fun y hy => h3 y hy))]; exact deriv_sub (h4 x hx).2 (h5 x hx).2

theorem thm_derivative_linear_1 (g : ℝ → ℝ) (D : Set ℝ) (U : Set ℝ) (h1 : D ⊆ (Set.univ : Set ℝ)) (h2 : U ⊆ D) (h3 : IsOpen U) (m : ℝ) (h5 : ∀ x ∈ D, g x = m * x) :
    ∀ x ∈ U, D ∈ nhds x ∧ DifferentiableAt ℝ g x :=
  fun x hx => ⟨Filter.mem_of_superset (h3.mem_nhds hx) h2, (show DifferentiableAt ℝ (fun y : ℝ => m * y) x by fun_prop).congr_of_eventuallyEq (Filter.eventually_of_mem (Filter.mem_of_superset (h3.mem_nhds hx) h2) (fun y hy => h5 y hy))⟩

theorem thm_derivative_linear_2 (g : ℝ → ℝ) (D : Set ℝ) (U : Set ℝ) (h1 : D ⊆ (Set.univ : Set ℝ)) (h2 : U ⊆ D) (h3 : IsOpen U) (m : ℝ) (h5 : ∀ x ∈ D, g x = m * x) :
    ∀ x ∈ U, (deriv g) x = m :=
  fun x hx => by rw [Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (Filter.mem_of_superset (h3.mem_nhds hx) h2) (fun y hy => h5 y hy))]; simpa using ((hasDerivAt_id x).const_mul m).deriv

theorem thm_derivative_square_1 (g : ℝ → ℝ) (D : Set ℝ) (U : Set ℝ) (h1 : D ⊆ (Set.univ : Set ℝ)) (h2 : U ⊆ D) (h3 : IsOpen U) (h4 : ∀ x ∈ D, g x = x ^ 2) :
    ∀ x ∈ U, D ∈ nhds x ∧ DifferentiableAt ℝ g x :=
  fun x hx => ⟨Filter.mem_of_superset (h3.mem_nhds hx) h2, (show DifferentiableAt ℝ (fun y : ℝ => y ^ 2) x by fun_prop).congr_of_eventuallyEq (Filter.eventually_of_mem (Filter.mem_of_superset (h3.mem_nhds hx) h2) (fun y hy => h4 y hy))⟩

theorem thm_derivative_square_2 (g : ℝ → ℝ) (D : Set ℝ) (U : Set ℝ) (h1 : D ⊆ (Set.univ : Set ℝ)) (h2 : U ⊆ D) (h3 : IsOpen U) (h4 : ∀ x ∈ D, g x = x ^ 2) :
    ∀ x ∈ U, (deriv g) x = 2 * x :=
  fun x hx => by rw [Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (Filter.mem_of_superset (h3.mem_nhds hx) h2) (fun y hy => h4 y hy))]; simpa using (hasDerivAt_pow 2 x).deriv

theorem thm_derivative_power_1 (g : ℝ → ℝ) (D : Set ℝ) (U : Set ℝ) (h1 : D ⊆ (Set.univ : Set ℝ)) (h2 : U ⊆ D) (h3 : IsOpen U) (n : ℤ) (h4 : 0 ≤ n) (h5 : ∀ x ∈ D, g x = x ^ (n + 1).toNat) :
    ∀ x ∈ U, D ∈ nhds x ∧ DifferentiableAt ℝ g x :=
  fun x hx => ⟨Filter.mem_of_superset (h3.mem_nhds hx) h2, (show DifferentiableAt ℝ (fun y : ℝ => y ^ (n + 1).toNat) x by fun_prop).congr_of_eventuallyEq (Filter.eventually_of_mem (Filter.mem_of_superset (h3.mem_nhds hx) h2) (fun y hy => h5 y hy))⟩

theorem thm_derivative_power_2 (g : ℝ → ℝ) (D : Set ℝ) (U : Set ℝ) (h1 : D ⊆ (Set.univ : Set ℝ)) (h2 : U ⊆ D) (h3 : IsOpen U) (n : ℤ) (h4 : 0 ≤ n) (h5 : ∀ x ∈ D, g x = x ^ (n + 1).toNat) :
    ∀ x ∈ U, (deriv g) x = ((n : ℝ) + 1) * x ^ n.toNat :=
  fun x hx => by lift n to ℕ using h4; rw [Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (Filter.mem_of_superset (h3.mem_nhds hx) h2) (fun y hy => h5 y hy))]; simp only [Int.toNat_natCast, show ((n : ℤ) + 1).toNat = n + 1 by omega]; simpa using (hasDerivAt_pow (n + 1) x).deriv

theorem thm_derivative_scaled_1 (F : ℝ → ℝ) (f : ℝ → ℝ) (D : Set ℝ) (U : Set ℝ) (h1 : D ⊆ (Set.univ : Set ℝ)) (h2 : U ⊆ D) (c : ℝ) (h4 : ∀ x ∈ D, F x = c * f x) (h5 : ∀ x ∈ U, D ∈ nhds x ∧ DifferentiableAt ℝ f x) :
    ∀ x ∈ U, D ∈ nhds x ∧ DifferentiableAt ℝ F x :=
  fun x hx => ⟨(h5 x hx).1, ((h5 x hx).2.const_mul c).congr_of_eventuallyEq (Filter.eventually_of_mem (h5 x hx).1 (fun y hy => h4 y hy))⟩

theorem thm_derivative_scaled_2 (F : ℝ → ℝ) (f : ℝ → ℝ) (D : Set ℝ) (U : Set ℝ) (h1 : D ⊆ (Set.univ : Set ℝ)) (h2 : U ⊆ D) (c : ℝ) (h4 : ∀ x ∈ D, F x = c * f x) (h5 : ∀ x ∈ U, D ∈ nhds x ∧ DifferentiableAt ℝ f x) :
    ∀ x ∈ U, (deriv F) x = c * (deriv f) x :=
  fun x hx => by rw [Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (h5 x hx).1 (fun y hy => h4 y hy))]; exact deriv_const_mul c (h5 x hx).2

theorem thm_area_function_1 (f : ℝ → ℝ) (G : ℝ → ℝ) (a : ℝ) (b : ℝ) (h3 : a < b) (h4 : ContinuousOn f (Set.Icc a b : Set ℝ)) (h5 : ∀ x ∈ (Set.Icc a b : Set ℝ), G x = (∫ t in a..x, (f t : ℝ))) :
    ContinuousOn G (Set.Icc a b : Set ℝ) :=
  by have hi : MeasureTheory.IntegrableOn f (Set.uIcc a b) := (by rw [Set.uIcc_of_le h3.le]; exact h4.integrableOn_Icc); have hc := intervalIntegral.continuousOn_primitive_interval hi; rw [Set.uIcc_of_le h3.le] at hc; exact hc.congr (fun x hx => h5 x hx)

theorem thm_area_function_2 (f : ℝ → ℝ) (G : ℝ → ℝ) (a : ℝ) (b : ℝ) (h3 : a < b) (h4 : ContinuousOn f (Set.Icc a b : Set ℝ)) (h5 : ∀ x ∈ (Set.Icc a b : Set ℝ), G x = (∫ t in a..x, (f t : ℝ))) :
    ∀ x ∈ (Set.Ioo a b : Set ℝ), (Set.Icc a b : Set ℝ) ∈ nhds x ∧ DifferentiableAt ℝ G x :=
  fun x hx => ⟨Icc_mem_nhds hx.1 hx.2, ((intervalIntegral.integral_hasDerivAt_right ((h4.mono (Set.Icc_subset_Icc le_rfl hx.2.le)).intervalIntegrable_of_Icc hx.1.le) ((h4.mono Set.Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo x hx) (h4.continuousAt (Icc_mem_nhds hx.1 hx.2))).congr_of_eventuallyEq (Filter.eventually_of_mem (Icc_mem_nhds hx.1 hx.2) (fun y hy => h5 y hy))).differentiableAt⟩

theorem thm_area_function_3 (f : ℝ → ℝ) (G : ℝ → ℝ) (a : ℝ) (b : ℝ) (h3 : a < b) (h4 : ContinuousOn f (Set.Icc a b : Set ℝ)) (h5 : ∀ x ∈ (Set.Icc a b : Set ℝ), G x = (∫ t in a..x, (f t : ℝ))) :
    ∀ x ∈ (Set.Ioo a b : Set ℝ), (deriv G) x = f x :=
  fun x hx => ((intervalIntegral.integral_hasDerivAt_right ((h4.mono (Set.Icc_subset_Icc le_rfl hx.2.le)).intervalIntegrable_of_Icc hx.1.le) ((h4.mono Set.Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo x hx) (h4.continuousAt (Icc_mem_nhds hx.1 hx.2))).congr_of_eventuallyEq (Filter.eventually_of_mem (Icc_mem_nhds hx.1 hx.2) (fun y hy => h5 y hy))).deriv

theorem mun_integral_real (f : ℝ → ℝ) (x : ℝ) (a : ℝ) (b : ℝ) (h3 : a < b) (h4 : ContinuousOn f (Set.Icc a b : Set ℝ)) (h5 : x ∈ (Set.Icc a b : Set ℝ)) :
    True :=
  by (simp_all; done)

theorem mun_integral_point (f : ℝ → ℝ) (X : Set ℝ) (a : ℝ) :
    (∫ t in a..a, (f t : ℝ)) = 0 :=
  by (simp_all; done)

theorem thm_integral_difference (f : ℝ → ℝ) (g : ℝ → ℝ) (h : ℝ → ℝ) (a : ℝ) (b : ℝ) (h3 : a < b) (h4 : ∀ x ∈ (Set.Icc a b : Set ℝ), h x = f x - g x) (h5 : ContinuousOn f (Set.Icc a b : Set ℝ)) (h6 : ContinuousOn g (Set.Icc a b : Set ℝ)) :
    (∫ t in a..b, (h t : ℝ)) = (∫ t in a..b, (f t : ℝ)) - (∫ t in a..b, (g t : ℝ)) :=
  by rw [← intervalIntegral.integral_sub (h5.intervalIntegrable_of_Icc h3.le) (h6.intervalIntegrable_of_Icc h3.le)]; apply intervalIntegral.integral_congr; intro x hx; rw [Set.uIcc_of_le h3.le] at hx; exact h4 x hx

theorem thm_integral_order (f : ℝ → ℝ) (g : ℝ → ℝ) (a : ℝ) (b : ℝ) (h3 : a < b) (h4 : ∀ x ∈ (Set.Icc a b : Set ℝ), f x ≤ g x) (h5 : ContinuousOn f (Set.Icc a b : Set ℝ)) (h6 : ContinuousOn g (Set.Icc a b : Set ℝ)) :
    (∫ t in a..b, (f t : ℝ)) ≤ (∫ t in a..b, (g t : ℝ)) :=
  intervalIntegral.integral_mono_on h3.le (h5.intervalIntegrable_of_Icc h3.le) (h6.intervalIntegrable_of_Icc h3.le) h4

theorem thm_integral_nonneg (f : ℝ → ℝ) (a : ℝ) (b : ℝ) (h3 : a < b) (h4 : ∀ x ∈ (Set.Icc a b : Set ℝ), 0 ≤ f x) (h5 : ContinuousOn f (Set.Icc a b : Set ℝ)) :
    0 ≤ (∫ t in a..b, (f t : ℝ)) :=
  intervalIntegral.integral_nonneg h3.le h4

theorem thm_cauchy_mean_value (f : ℝ → ℝ) (g : ℝ → ℝ) (D : Set ℝ) (h1 : D ⊆ (Set.univ : Set ℝ)) (a : ℝ) (b : ℝ) (h4 : a < b) (h5 : (Set.Icc a b : Set ℝ) ⊆ D) (h6 : ContinuousOn f (Set.Icc a b : Set ℝ)) (h7 : ContinuousOn g (Set.Icc a b : Set ℝ)) (h8 : ∀ x ∈ (Set.Ioo a b : Set ℝ), D ∈ nhds x ∧ DifferentiableAt ℝ f x) (h9 : ∀ x ∈ (Set.Ioo a b : Set ℝ), D ∈ nhds x ∧ DifferentiableAt ℝ g x) :
    ∃ c ∈ (Set.Ioo a b : Set ℝ), (f b - f a) * (deriv g) c = (g b - g a) * (deriv f) c :=
  exists_ratio_deriv_eq_ratio_slope g h4 h7 (fun x hx => (h9 x hx).2.differentiableWithinAt) f h6 (fun x hx => (h8 x hx).2.differentiableWithinAt)

theorem thm_limit_at_most (x : ℤ → ℝ) (L : ℝ) (h2 : Filter.Tendsto (fun n : ℤ => (x n : ℝ)) Filter.atTop (nhds L)) (B : ℝ) (N : ℤ) (h4 : 0 < N) (h5 : ∀ n : ℤ, 0 < n → N ≤ n → x n ≤ B) :
    L ≤ B :=
  le_of_tendsto h2 (Filter.eventually_atTop.2 ⟨N, fun n hn => h5 n (by omega) hn⟩)

theorem thm_limit_at_least (x : ℤ → ℝ) (L : ℝ) (h2 : Filter.Tendsto (fun n : ℤ => (x n : ℝ)) Filter.atTop (nhds L)) (B : ℝ) (N : ℤ) (h4 : 0 < N) (h5 : ∀ n : ℤ, 0 < n → N ≤ n → B ≤ x n) :
    B ≤ L :=
  ge_of_tendsto h2 (Filter.eventually_atTop.2 ⟨N, fun n hn => h5 n (by omega) hn⟩)

theorem mun_first_terms_bounded (x : ℤ → ℝ) :
    ∀ K : ℤ, 0 < K → (∃ C : ℝ, ∀ m : ℤ, m ∈ Finset.Icc 1 K → abs (x m) ≤ C) :=
  fun K _ => ⟨∑ m ∈ Finset.Icc 1 (K : ℤ), |x m|, fun m hm => Finset.single_le_sum (f := fun m => |x m|) (fun i _ => abs_nonneg _) hm⟩

theorem thm_convergent_abs_bounded (x : ℤ → ℝ) (L : ℝ) (h2 : Filter.Tendsto (fun n : ℤ => (x n : ℝ)) Filter.atTop (nhds L)) :
    ∃ B : ℝ, ∀ m : ℤ, 0 < m → abs (x m) ≤ B :=
  by have h := h2.comp tendsto_natCast_atTop_atTop; obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto _ h); exact ⟨C, fun m hm => by have := hC _ ⟨m.toNat, rfl⟩; simpa [Real.norm_eq_abs, Int.toNat_of_nonneg hm.le] using this⟩

theorem thm_convergent_bounded (x : ℤ → ℝ) (L : ℝ) (h2 : Filter.Tendsto (fun n : ℤ => (x n : ℝ)) Filter.atTop (nhds L)) :
    ∃ B : ℝ, ∀ m : ℤ, 0 < m → x m ≤ B :=
  by have h := h2.comp tendsto_natCast_atTop_atTop; obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto _ h); exact ⟨C, fun m hm => le_trans (le_abs_self _) (by have := hC _ ⟨m.toNat, rfl⟩; simpa [Real.norm_eq_abs, Int.toNat_of_nonneg hm.le] using this)⟩

theorem thm_monotone_limit (x : ℤ → ℝ) (h1 : ∀ n : ℤ, 0 < n → x n ≤ x (n + 1)) (B : ℝ) (h3 : ∀ n : ℤ, 0 < n → x n ≤ B) :
    ∃ L : ℝ, Filter.Tendsto (fun n : ℤ => (x n : ℝ)) Filter.atTop (nhds L) :=
  by have hmono : Monotone (fun n : ℤ => x (max n 1)) := (monotone_int_of_le_succ (fun n => by rcases le_or_gt n 0 with h | h; (rw [max_eq_right (by omega), max_eq_right (by omega)]); (rw [max_eq_left (by omega), max_eq_left (by omega)]; exact h1 n h))); have hbdd : BddAbove (Set.range fun n : ℤ => x (max n 1)) := ⟨B, by rintro _ ⟨n, rfl⟩; exact h3 _ (by omega)⟩; exact ⟨⨆ n : ℤ, x (max n 1), (tendsto_atTop_ciSup hmono hbdd).congr' (Filter.eventually_atTop.2 ⟨1, fun n hn => by simp only [max_eq_left hn]⟩)⟩

theorem def_upper_bound {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] (S : Set K) (u : K) :
    (∀ s ∈ S, s ≤ u) ↔ (∀ s ∈ S, s ≤ u) :=
  Iff.rfl

theorem def_least_upper_bound {K : Type*} [CommRing K] [IsDomain K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K] (S : Set K) (c : K) :
    (∀ s ∈ S, s ≤ c) ∧ (∀ u : K, (∀ s ∈ S, s ≤ u) → c ≤ u) ↔ (∀ s ∈ S, s ≤ c) ∧ (∀ u : K, (∀ s ∈ S, s ≤ u) → c ≤ u) :=
  Iff.rfl

end Parley.Items.Stdlib.Calculus
