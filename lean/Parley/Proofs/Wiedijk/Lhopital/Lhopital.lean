module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Wiedijk.Lhopital.QuotientBetween

/-! Written from proofs/wiedijk/lhopital.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Lhopital.Lhopital

theorem lhopital (a : ℝ) (b : ℝ) (c : ℝ) (hH3 : c ∈ (Set.Ioo a b : Set ℝ)) (L : ℝ) (f : ℝ → ℝ) (hH5 : Set.MapsTo f ((Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)) (Set.univ : Set ℝ)) (g : ℝ → ℝ) (hH6 : Set.MapsTo g ((Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)) (Set.univ : Set ℝ)) (hH7 : ∀ x ∈ ((Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)), ((Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)) ∈ nhds x ∧ DifferentiableAt ℝ f x) (hH8 : ∀ x ∈ ((Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)), ((Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)) ∈ nhds x ∧ DifferentiableAt ℝ g x) (hH9 : Filter.Tendsto f (nhdsWithin c (((Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)) \ {c})) (nhds 0)) (hH10 : Filter.Tendsto g (nhdsWithin c (((Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)) \ {c})) (nhds 0)) (hH11 : ∀ x ∈ (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ), (deriv g) x ≠ 0) (q : ℝ → ℝ) (hD1 : ∀ x : ℝ, x ∈ (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ) → q x = (deriv f) x / (deriv g) x) (r : ℝ → ℝ) (hD2 : ∀ x : ℝ, x ∈ (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ) → r x = f x / g x) (hH12 : Filter.Tendsto q (nhdsWithin c (((Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)) \ {c})) (nhds L)) :
    Filter.Tendsto r (nhdsWithin c (((Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)) \ {c})) (nhds L) := by
  -- 1. mun:open-interval-real
  have s1 : (Set.Ioo a b : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_interval_real (a := a) (b := b))
  -- 2. mun:subset-transitive X := (a, b) ∖ {c}, Y := (a, b), Z := ℝ, from 1
  have r564_1 : (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ) ⊆ (Set.Ioo a b : Set ℝ) := by exact (Parley.Items.Stdlib.Sets.mun_difference_subset (X := (Set.Ioo a b : Set ℝ)) (Y := ({c} : Set ℝ)))
  have s2 : (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)) (Y := (Set.Ioo a b : Set ℝ)) (Z := (Set.univ : Set ℝ)) r564_1 s1)
  -- 3. mun:subset-self
  have s3 : (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ) ⊆ (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ) := by exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)))
  -- 4. membership, from D1
  have r571_3 : ∀ x ∈ (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ), (deriv g) x ≠ 0 := by exact hH11
  have s4 : ∀ x ∈ (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ), True := by intro x h_x; exact by trivial
  -- 5. mun:function-into, from 4
  have s5 : Set.MapsTo q ((Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)) (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := q) (X := (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by intro x _; exact Set.mem_univ _))
  -- 6. thm:quotient-between f := f, from H3, H7, H8, H9, H10, H11
  have s6 : ∀ x ∈ (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ), g x ≠ 0 := by intro x h_x; (exact (Parley.Proofs.Wiedijk.Lhopital.QuotientBetween.quotient_between (a := a) (b := b) (c := c) hH3 (f := f) (Set.mapsTo_univ _ _) (g := g) (Set.mapsTo_univ _ _) hH7 hH8 hH9 hH10 hH11 (x := x) h_x).1)
  -- 7. membership, from D2
  have r584_3 : ∀ x ∈ (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ), g x ≠ 0 := by exact s6
  have s7 : ∀ x ∈ (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ), True := by intro x h_x; exact by trivial
  -- 8. mun:function-into, from 7
  have s8 : Set.MapsTo r ((Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)) (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := r) (X := (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by intro x _; exact Set.mem_univ _))
  -- 9. def:limit-at D := (a, b) ∖ {c}, f := q, from H12, 2, 5
  have s9 : ∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ (∀ x ∈ (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ), x ≠ c ∧ abs (x - c) < δ → abs (q x - L) < ε)) := by exact ((Parley.Items.Stdlib.Calculus.def_limit_at (f := q) (D := (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)) s2 (c := c) (L := L))).mp hH12
  -- 10. proof
  have s10 : ∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ (∀ x ∈ (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ), x ≠ c ∧ abs (x - c) < δ → abs (r x - L) < ε)) := by
    intro ε
    intro hA1
    -- 10.1. instantiate ε := ε in line 9, from A1
    have s10_1 : ∃ δ : ℝ, δ > 0 ∧ (∀ x ∈ (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ), x ≠ c ∧ abs (x - c) < δ → abs (q x - L) < ε) := by exact (s9 ε hA1)
    -- 10.2. obtain δ from line 10.1
    obtain ⟨δ, ⟨s10_2a, s10_2b⟩⟩ := s10_1
    -- 10.3. proof
    have s10_3 : ∀ x ∈ (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ), x ≠ c ∧ abs (x - c) < δ → abs (r x - L) < ε := by
      intro x hK2
      intro hA2
      -- 10.3.1. obtain ξ: thm:quotient-between, from H3, H7, H8, H9, H10, H11, K2
      obtain ⟨ξ, s10_3_1a, s10_3_1b⟩ := (Parley.Proofs.Wiedijk.Lhopital.QuotientBetween.quotient_between (a := a) (b := b) (c := c) hH3 (f := f) (Set.mapsTo_univ _ _) (g := g) (Set.mapsTo_univ _ _) hH7 hH8 hH9 hH10 hH11 (x := x) hK2).2
      -- 10.3.2. transitivity, from 10.3.1, A2
      have s10_3_2 : abs (ξ - c) < δ := by exact lt_trans s10_3_1b.1 hA2.2
      -- 10.3.3. mun:remove-member, from 10.3.1
      have s10_3_3 : ξ ∈ (Set.Ioo a b : Set ℝ) ∧ ξ ≠ c := by exact ((Parley.Items.Stdlib.Sets.mun_remove_member (Y := (Set.Ioo a b : Set ℝ)) (a := c) (u := ξ))).mp s10_3_1a
      -- 10.3.4. instantiate x := ξ in line 10.2, from 10.3.1, 10.3.2, 10.3.3
      have s10_3_4 : abs (q ξ - L) < ε := by exact (s10_2b ξ s10_3_1a ⟨s10_3_3.2, s10_3_2⟩)
      -- 10.3.5. D1, from 10.3.1
      have s10_3_5 : q ξ = (deriv f) ξ / (deriv g) ξ := by simp (disch := omega) only [hD1]
      -- 10.3.6. D2, from K2
      have s10_3_6 : r x = f x / g x := by simp (disch := omega) only [hD2]
      -- 10.3.7. calculation
      have s10_3_7 : r x = q ξ := by
        calc r x = f x / g x := s10_3_6
          _ = (deriv f) ξ / (deriv g) ξ := s10_3_1b.2
          _ = q ξ := s10_3_5.symm
      -- 10.3.8. substitute r(x) = q(ξ) (line 10.3.7) into line 10.3.4
      exact Eq.subst (motive := (fun t : ℝ => abs (t - L) < ε)) s10_3_7.symm s10_3_4
    -- 10.4. exhibit, from 10.2, 10.3
    exact ⟨δ, ⟨s10_2a, s10_3⟩⟩
  -- 11. def:limit-at D := (a, b) ∖ {c}, f := r, from 2, 8, 10
  exact ((Parley.Items.Stdlib.Calculus.def_limit_at (f := r) (D := (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)) s2 (c := c) (L := L))).mpr s10

end Parley.Proofs.Wiedijk.Lhopital.Lhopital
