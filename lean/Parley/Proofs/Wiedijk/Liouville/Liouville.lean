module

public import Polynomials
public import PowerTactics
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.Data.Rat.Cast.Lemmas
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Polynomials
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Wiedijk.Liouville.NearARoot
public import Parley.Proofs.Wiedijk.Liouville.ValueAtAFraction

/-! Written from proofs/wiedijk/liouville.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Liouville.Liouville

theorem liouville (F : ℂ → ℂ) (hH2 : F ∈ LeanBridges.Polynomials.integerPolynomials) (N : ℤ) (hH3 : 0 < N) (hH4 : (LeanBridges.Polynomials.degree F : ℤ) = N) (α : ℝ) (hH6 : F (α : ℂ) = 0) :
    (∃ c : ℝ, c > 0 ∧ (∀ p : ℤ, ∀ q : ℤ, 0 < q → α = (p : ℝ) / (q : ℝ) ∨ c / (q : ℝ) ^ N.toNat < abs (α - (p : ℝ) / (q : ℝ)))) := by
  set f : ℝ → ℂ := fun x : ℝ => F (x : ℂ) with hD1
  -- 1. D1
  have s1 : ∀ x : ℝ, f x = F (x : ℂ) := by simp (disch := omega) only [hD1, implies_true]
  -- 2. mun:integer-polynomial-real, from D1, H2
  have s2 : ∀ x : ℝ, ∃ m : ℝ, (m : ℂ) = f x := by
    intro x
    simp only [hD1] at ⊢
    push_cast at ⊢
    exact (Parley.Items.Stdlib.Polynomials.mun_integer_polynomial_real (F := F) hH2 (x := x))
  obtain ⟨f, s2_eq⟩ : ∃ f' : ℝ → ℝ, ∀ x : ℝ, (f' x : ℂ) = f x := ⟨fun x => (s2 x).choose, fun x => (s2 x).choose_spec⟩
  have hD1_f : ∀ x : ℝ, (f x : ℂ) = F (x : ℂ) := fun x => (s2_eq x).trans (by simp only [hD1])
  -- 3. mun:function-into, from 2
  -- 4. thm:polynomial-on-the-reals, from H2, 1, 3
  have s4a : ContinuousOn f (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Polynomials.thm_polynomial_on_the_reals_1 (F := F) (f := f) hH2 (show ∀ x : ℝ, (f x : ℂ) = F (x : ℂ) by have h := s1; simp only [← s2_eq] at h; exact_mod_cast h))
  have s4b : ∀ x ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ f x := by exact (Parley.Items.Stdlib.Polynomials.thm_polynomial_on_the_reals_2 (F := F) (f := f) hH2 (show ∀ x : ℝ, (f x : ℂ) = F (x : ℂ) by have h := s1; simp only [← s2_eq] at h; exact_mod_cast h))
  have s4c : ContinuousOn (deriv f) (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Polynomials.thm_polynomial_on_the_reals_4 (F := F) (f := f) hH2 (show ∀ x : ℝ, (f x : ℂ) = F (x : ℂ) by have h := s1; simp only [← s2_eq] at h; exact_mod_cast h))
  -- 5. D1, from H5
  have s5 : (f α : ℂ) = F (α : ℂ) := by simp (disch := omega) only [hD1_f]
  -- 6. calculation
  have s6 : f α = 0 := by
    have h := by
      calc (f α : ℂ) = F (α : ℂ) := s5
        _ = 0 := hH6
    exact_mod_cast h
  -- 7. obtain δ: thm:roots-isolated, from H2, H4, H6
  obtain ⟨δ, ⟨s7a, s7b⟩⟩ := (Parley.Items.Stdlib.Polynomials.thm_roots_isolated (F := F) hH2 (N := N) hH3 hH4 (α := α) hH6)
  -- 8. mun:interval-real
  have s8 : (Set.Icc (α - 1) (α + 1) : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_interval_real (a := α - 1) (b := α + 1))
  -- 9. mun:subset-self
  have s9 : (Set.univ : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ)))
  -- 10. mun:continuous-on-part D := ℝ, f := f′, S := [α − 1, α + 1], from 4, 8, 9
  have s10 : ContinuousOn (deriv f) (Set.Icc (α - 1) (α + 1) : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_continuous_on_part (f := (deriv f)) (D := (Set.univ : Set ℝ)) (S := (Set.Icc (α - 1) (α + 1) : Set ℝ)) s9 s8 s4c)
  -- 11. mun:map-continuous-on-part D := ℝ, S := [α − 1, α + 1], f := f′, from 4, 8, 9, 10
  have s11 : ContinuousOn (fun t : ℝ => (deriv f) t) (Set.Icc (α - 1) (α + 1) : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_map_continuous_on_part (f := (deriv f)) (D := (Set.univ : Set ℝ)) (S := (Set.Icc (α - 1) (α + 1) : Set ℝ)) s9 s8 s10)
  -- 12. mun:derivative-real-on D := ℝ, U := ℝ, x := t, from 3, 4, 9
  have s12 : ∀ t ∈ (Set.Icc (α - 1) (α + 1) : Set ℝ), True := by intro t h_t; (trivial)
  -- 13. mun:function-into, from 12
  have s13 : Set.MapsTo (fun t : ℝ => (deriv f) t) (Set.Icc (α - 1) (α + 1) : Set ℝ) (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := (fun t : ℝ => (deriv f) t)) (X := (Set.Icc (α - 1) (α + 1) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by intro x _; exact Set.mem_univ _))
  -- 14. obtain M: thm:continuous-bounded a := α − 1, b := α + 1, f := (t ∈ [α − 1, α + 1] ↦ f′(t)), from 11, 13
  obtain ⟨M, s14⟩ := (Parley.Items.Stdlib.Calculus.thm_continuous_bounded (f := (fun t : ℝ => (deriv f) t)) (a := α - 1) (b := α + 1) s11)
  set K : ℝ := max M 1 with hD2
  -- 15. mun:le-max x := M, y := 1, from D2
  have s15 : 1 ≤ K := by
    simp only [hD2] at ⊢
    exact (Parley.Items.Stdlib.Numbers.mun_le_max_2 (x := M) (y := (1 : ℝ)))
  -- 16. inequalities, from 15
  have s16 : K > 0 := by linarith only [s15]
  -- 17. proof
  have s17 : ∀ t ∈ (Set.Icc (α - 1) (α + 1) : Set ℝ), abs ((deriv f) t) ≤ K := by
    intro t hK2
    -- 17.1. instantiate x := t in line 14, from K2
    have s17_1 : abs ((deriv f) t) ≤ M := by exact (s14 t hK2)
    -- 17.2. mun:le-max x := M, y := 1, from D2
    have s17_2 : M ≤ K := by
      simp only [hD2] at ⊢
      exact (Parley.Items.Stdlib.Numbers.mun_le_max_1 (x := M) (y := (1 : ℝ)))
    -- 17.3. transitivity, from 17.1, 17.2
    exact le_trans s17_1 s17_2
  -- 18. mun:min-real x := 1, y := δ
  -- 19. inequalities
  have s19 : 2 * K > 0 := by linarith only [s16]
  -- 20. membership
  have r504_1 : 2 * K ≠ 0 := ne_of_gt (by linarith only [s19])
  set c : ℝ := min (min 1 δ) (1 / (2 * K)) with hD3
  -- 21. mun:reciprocal-positive x := 2K, from 19
  have s21 : 0 < 1 / (2 * K) := by exact (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := 2 * K) s19)
  -- 22. mun:lt-min z := 0, x := 1, y := δ, from 7
  have r515_1 : (0 : ℤ) < 1 := by norm_num
  have s22 : 0 < min 1 δ := ((Parley.Items.Stdlib.Numbers.mun_lt_min (z := (0 : ℝ)) (x := (1 : ℝ)) (y := δ))).mpr ⟨by norm_num, s7a⟩
  -- 23. mun:lt-min z := 0, x := min(1, δ), y := 1/(2K), from D3, 18, 20, 21, 22
  have s23 : 0 < c := ((Parley.Items.Stdlib.Numbers.mun_lt_min (z := (0 : ℝ)) (x := min 1 δ) (y := 1 / (2 * K)))).mpr ⟨s22, s21⟩
  -- 24. mun:min-le x := min(1, δ), y := 1/(2K), from D3, 18, 20
  have s24a : c ≤ min 1 δ := by
    simp only [hD3] at ⊢
    exact (Parley.Items.Stdlib.Numbers.mun_min_le_1 (x := min 1 δ) (y := 1 / (2 * K)))
  have s24b : c ≤ 1 / (2 * K) := by
    simp only [hD3] at ⊢
    exact (Parley.Items.Stdlib.Numbers.mun_min_le_2 (x := min 1 δ) (y := 1 / (2 * K)))
  -- 25. mun:min-le x := 1, y := δ
  have s25a : min 1 δ ≤ 1 := by exact (Parley.Items.Stdlib.Numbers.mun_min_le_1 (x := (1 : ℝ)) (y := δ))
  have s25b : min 1 δ ≤ δ := by exact (Parley.Items.Stdlib.Numbers.mun_min_le_2 (x := (1 : ℝ)) (y := δ))
  -- 26. proof
  have s26 : ∀ p : ℤ, ∀ q : ℤ, 0 < q → α = (p : ℝ) / (q : ℝ) ∨ c / (q : ℝ) ^ N.toNat < abs (α - (p : ℝ) / (q : ℝ)) := by
    intro p
    intro q hK4
    -- 26.1. axi:excluded-middle
    have s26_1 : abs (α - (p : ℝ) / (q : ℝ)) ≤ min 1 δ ∨ ¬ abs (α - (p : ℝ) / (q : ℝ)) ≤ min 1 δ := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := abs (α - (p : ℝ) / (q : ℝ)) ≤ min 1 δ))
    -- 26.2. mun:power-positive a := q, m := N
    have r536_1 : q > 0 := by linarith only [hK4]
    have s26_2 : q ^ N.toNat > 0 := by (have h := (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (q : ℚ)) (m := N) (by exact_mod_cast gt_iff_lt.mp r536_1)); simp only [parley_zpow_toNat (n := N) (h := le_of_lt hH3)] at h ⊢; exact_mod_cast h)
    -- 26.3. cases, from 26.1
    rcases s26_1 with hC1 | hC4
    · skip
      -- 26.3.1. transitivity, from C1, 25
      have s26_3_1 : abs (α - (p : ℝ) / (q : ℝ)) ≤ 1 := by exact le_trans hC1 s25a
      -- 26.3.2. transitivity, from C1, 25
      have s26_3_2 : abs (α - (p : ℝ) / (q : ℝ)) ≤ δ := by exact le_trans hC1 s25b
      -- 26.3.3. axi:excluded-middle
      have s26_3_3 : F ((p : ℂ) / (q : ℂ)) = 0 ∨ F ((p : ℂ) / (q : ℂ)) ≠ 0 := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := F ((p : ℂ) / (q : ℂ)) = 0))
      -- 26.3.4. cases, from 26.3.3
      rcases s26_3_3 with hC2 | hC3
      · skip
        -- 26.3.4.1. instantiate r := p/q in line 7, from C2, 26.3.2
        have s26_3_4_1 : (p : ℝ) / (q : ℝ) = α := by exact (s7b ((p : ℝ) / (q : ℝ)) ⟨s26_3_2, by (have h := hC2; push_cast at h ⊢; exact h)⟩)
        -- 26.3.4.2. mun:or-left, from 26.3.4.1
        exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := α = (p : ℝ) / (q : ℝ)) (Q := c / (q : ℝ) ^ N.toNat < abs (α - (p : ℝ) / (q : ℝ))) s26_3_4_1.symm)
      · skip
        -- 26.3.4.3. thm:value-at-a-fraction, from C3, H2, H4
        have s26_3_4_3 : ‖F ((p : ℂ) / (q : ℂ))‖ ≥ 1 / (q : ℝ) ^ N.toNat := by exact (Parley.Proofs.Wiedijk.Liouville.ValueAtAFraction.value_at_a_fraction (F := F) hH2 (N := N) hH3 hH4 (p := p) (q := q) hK4 hC3)
        -- 26.3.4.4. D1
        have s26_3_4_4 : (f ((p : ℝ) / (q : ℝ)) : ℂ) = F ((p : ℂ) / (q : ℂ)) := by simp (disch := omega) only [hD1_f]; push_cast; norm_num
        -- 26.3.4.5. thm:near-a-root x := p/q, from 3, 4, 6, 16, 17, 26.3.1
        have s26_3_4_5 : abs (f ((p : ℝ) / (q : ℝ))) ≤ K * abs (α - (p : ℝ) / (q : ℝ)) := by exact (Parley.Proofs.Wiedijk.Liouville.NearARoot.near_a_root (f := f) s4a (by simp only [Filter.univ_mem, true_and]; exact s4b) (α := α) s6 (K := K) s16 s17 (x := (p : ℝ) / (q : ℝ)) s26_3_1)
        -- 26.3.4.6. substitute f(p/q) = F(p/q) (line 26.3.4.4) into line 26.3.4.5
        have s26_3_4_6 : ‖F ((p : ℂ) / (q : ℂ))‖ ≤ K * abs (α - (p : ℝ) / (q : ℝ)) := by
          have e_line : ‖(f ((p : ℝ) / (q : ℝ)) : ℂ)‖ ≤ K * abs (α - (p : ℝ) / (q : ℝ)) := by exact_mod_cast s26_3_4_5
          exact Eq.subst (motive := (fun t : ℂ => ‖t‖ ≤ K * abs (α - (p : ℝ) / (q : ℝ)))) s26_3_4_4 e_line
        -- 26.3.4.7. transitivity, from 26.3.4.3, 26.3.4.6
        have r584_1 : ∃ m : ℝ, (m : ℂ) = F ((p : ℂ) / (q : ℂ)) := by
          have hI : ∃ m : ℝ, (m : ℂ) = F ((p : ℂ) / (q : ℂ)) := by (have h := ((Parley.Items.Stdlib.Polynomials.mun_integer_polynomial_real (F := F) hH2 (x := (p : ℝ) / (q : ℝ)))); push_cast at h ⊢; exact h)
          exact hI
        have s26_3_4_7 : 1 / (q : ℝ) ^ N.toNat ≤ K * abs (α - (p : ℝ) / (q : ℝ)) := by exact le_trans s26_3_4_3 s26_3_4_6
        -- 26.3.4.8. mun:divide-le x := 1/q^N, y := K·|α − p/q|, c := K, from 16, 26.3.4.7
        have s26_3_4_8 : 1 / (q : ℝ) ^ N.toNat / K ≤ K * abs (α - (p : ℝ) / (q : ℝ)) / K := by exact (Parley.Items.Stdlib.Numbers.mun_divide_le (x := 1 / (q : ℝ) ^ N.toNat) (y := K * abs (α - (p : ℝ) / (q : ℝ))) (c := K) s26_3_4_7 s16)
        -- 26.3.4.9. algebra
        have r591_1 : K ≠ 0 := ne_of_gt (by linarith only [s16])
        have s26_3_4_9 : K * abs (α - (p : ℝ) / (q : ℝ)) / K = abs (α - (p : ℝ) / (q : ℝ)) := by have hz1 : K ≠ 0 := r591_1; field
        -- 26.3.4.10. mun:divide-le x := c, y := 1/(2K), c := q^N, from 20, 24, 26.2
        have s26_3_4_10 : c / (q : ℝ) ^ N.toNat ≤ 1 / (2 * K) / (q : ℝ) ^ N.toNat := by exact (Parley.Items.Stdlib.Numbers.mun_divide_le (x := c) (y := 1 / (2 * K)) (c := (q : ℝ) ^ N.toNat) s24b (by exact_mod_cast gt_iff_lt.mp s26_2))
        -- 26.3.4.11. algebra
        have r598_1 : K ≠ 0 := ne_of_gt (by linarith only [s16])
        have s26_3_4_11 : 1 / (2 * K) / (q : ℝ) ^ N.toNat = 1 / (q : ℝ) ^ N.toNat / K / 2 := by have hz1 : K ≠ 0 := r598_1; have hz2 : (q : ℝ) ^ N.toNat ≠ 0 := (by positivity); field
        -- 26.3.4.12. mun:reciprocal-positive x := q^N, from 26.2
        have s26_3_4_12 : 1 / (q : ℚ) ^ N.toNat > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (q : ℚ) ^ N.toNat) (by exact_mod_cast gt_iff_lt.mp s26_2))
        -- 26.3.4.13. mun:quotient-positive x := 1/q^N, y := K, from 16, 26.3.4.12
        have s26_3_4_13 : 1 / (q : ℝ) ^ N.toNat / K > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := 1 / (q : ℝ) ^ N.toNat) (y := K) (show 0 < 1 / (q : ℝ) ^ N.toNat by have h := (Rat.cast_lt (K := ℝ)).mpr (gt_iff_lt.mp s26_3_4_12); simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_zero, Rat.cast_one, Rat.cast_intCast] at h; exact h) s16)
        -- 26.3.4.14. inequalities
        have r608_1 : K ≠ 0 := ne_of_gt (by linarith only [s16])
        have s26_3_4_14 : 1 / (q : ℝ) ^ N.toNat / K / 2 < 1 / (q : ℝ) ^ N.toNat / K := by linarith only [s26_3_4_13]
        -- 26.3.4.15. transitivity, from 26.3.4.10, 26.3.4.11, 26.3.4.14, 26.3.4.8, 26.3.4.9
        have r616_1 : K ≠ 0 := ne_of_gt (by linarith only [s16])
        have s26_3_4_15 : c / (q : ℝ) ^ N.toNat < abs (α - (p : ℝ) / (q : ℝ)) := by exact LT.lt.trans_eq (lt_of_lt_of_le (lt_of_le_of_lt (LE.le.trans_eq s26_3_4_10 s26_3_4_11) s26_3_4_14) s26_3_4_8) s26_3_4_9
        -- 26.3.4.16. mun:or-right, from 26.3.4.15
        exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := α = (p : ℝ) / (q : ℝ)) (Q := c / (q : ℝ) ^ N.toNat < abs (α - (p : ℝ) / (q : ℝ))) s26_3_4_15)
    · skip
      -- 26.3.5. inequalities, from C4
      have s26_3_5 : min 1 δ < abs (α - (p : ℝ) / (q : ℝ)) := by linarith only [hC4]
      -- 26.3.6. mun:power-at-least-one a := q, n := N
      have r630_1 : 1 ≤ q := by linarith only [hK4]
      have s26_3_6 : 1 ≤ q ^ N.toNat := by exact (Parley.Items.Stdlib.Numbers.mun_power_at_least_one (a := q) (n := N) (le_of_lt hH3) r630_1)
      -- 26.3.7. mun:quotients-compared x := c, y := q^N, z := c, w := 1, from 26.3.6
      have r634_1 : 0 ≤ c := by linarith only [s23]
      have r634_2 : c ≤ c := by linarith
      have r634_3 : (0 : ℤ) < 1 := by norm_num
      have s26_3_7 : c / (q : ℝ) ^ N.toNat ≤ c / 1 := by exact (Parley.Items.Stdlib.Numbers.mun_quotients_compared (x := c) (y := (q : ℝ) ^ N.toNat) (z := c) (w := (1 : ℝ)) r634_1 r634_2 (by norm_num) (by exact_mod_cast s26_3_6))
      -- 26.3.8. algebra
      have s26_3_8 : c / 1 = c := by ring_nf
      -- 26.3.9. transitivity, from 26.3.7, 26.3.8, 24, 26.3.5
      have s26_3_9 : c / (q : ℝ) ^ N.toNat < abs (α - (p : ℝ) / (q : ℝ)) := by exact lt_of_le_of_lt (le_trans (LE.le.trans_eq s26_3_7 s26_3_8) s24a) s26_3_5
      -- 26.3.10. mun:or-right, from 26.3.9
      exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := α = (p : ℝ) / (q : ℝ)) (Q := c / (q : ℝ) ^ N.toNat < abs (α - (p : ℝ) / (q : ℝ))) s26_3_9)
  -- 27. exhibit, from 23, 26
  exact ⟨c, ⟨s23, s26⟩⟩

end Parley.Proofs.Wiedijk.Liouville.Liouville
