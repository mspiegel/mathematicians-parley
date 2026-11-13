module

public import InstanceTactics
public import NormTactics
public import SetTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/wiedijk/wilson.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Wilson.PairedProduct

theorem paired_product (X : Set ℤ) (hH1 : X ⊆ (Set.univ : Set ℤ)) (hH2 : X.Finite) (n : ℤ) (hH3 : 0 < n) (f : ℤ → ℤ) (hH4 : Set.MapsTo f X X) (hH5 : ∀ x ∈ X, f (f x) = x) (hH6 : ∀ x ∈ X, f x ≠ x) (hH7 : ∀ x ∈ X, x * f x ≡ (1 : ℤ) [ZMOD n]) :
    (∏ᶠ x ∈ X, (x : ℤ)) ≡ (1 : ℤ) [ZMOD n] := by
  set L : Set ℤ := {x ∈ X | x < f x} with hD1
  have hD1_finite : L.Finite := by rw [hD1]; exact (hH2).subset (fun _ h => h.1)
  set U : Set ℤ := {x ∈ X | ¬ x < f x} with hD2
  have hD2_finite : U.Finite := by rw [hD2]; exact (hH2).subset (fun _ h => h.1)
  -- 1. mun:set-builder-split, from D1, D2
  have s1 : X = L ∪ U := by
    try simp only [hD1, hD2] at ⊢
    try push_cast at ⊢
    exact (Parley.Items.Stdlib.Sets.mun_set_builder_split (P := (fun x : ℤ => x < f x)) (X := X))
  -- 2. mun:set-builder-split-disjoint, from D1, D2
  have s2 : L ∩ U = ∅ := by
    try simp only [hD1, hD2] at ⊢
    try push_cast at ⊢
    exact (Parley.Items.Stdlib.Sets.mun_set_builder_split_disjoint (P := (fun x : ℤ => x < f x)) (X := X))
  -- 3. mun:set-builder-subset, from D1
  have s3 : L ⊆ X := by
    try simp only [hD1] at ⊢
    try push_cast at ⊢
    exact (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun x : ℤ => x < f x)) (X := X))
  -- 4. mun:set-builder-subset, from D2
  have s4 : U ⊆ X := by
    try simp only [hD2] at ⊢
    try push_cast at ⊢
    exact (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun x : ℤ => ¬ x < f x)) (X := X))
  -- 5. mun:finite-part, from H2, 3
  have s5 : L.Finite := by exact (Parley.Items.Stdlib.Counting.mun_finite_part (X := X) (Y := L) hH2 s3)
  -- 6. mun:subset-transitive, from H1, 3
  have s6 : L ⊆ (Set.univ : Set ℤ) := by exact (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := L) (Y := X) (Z := (Set.univ : Set ℤ)) s3 hH1)
  -- 7. mun:subset-transitive, from H1, 4
  have s7 : U ⊆ (Set.univ : Set ℤ) := by exact (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := U) (Y := X) (Z := (Set.univ : Set ℤ)) s4 hH1)
  -- 8. proof
  have s8 : ∀ x ∈ L, f x ∈ U := by
    intro x hK1
    -- 8.1. def:set-builder u := x, from D1, K1
    have s8_1a : x ∈ X := by
      try simp only [hD1] at ⊢
      try push_cast at ⊢
      exact (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun x : ℤ => x < f x)) (X := X) (u := x))).mp hK1).1
    have s8_1b : x < f x := by
      try simp only [hD1] at ⊢
      try push_cast at ⊢
      have hI : x < f x := by parley_instance ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun x : ℤ => x < f x)) (X := X) (u := x))).mp hK1).2)
      exact hI
    -- 8.2. instantiate x := x in H5, from 8.1
    have s8_2 : f (f x) = x := by exact (hH5 x s8_1a)
    -- 8.3. mun:in-subset, from H1, 8.1
    -- 8.4. mun:in-subset, from H1, H4, 8.1
    -- 8.5. membership, from 8.2, 8.3
    -- 8.6. calculation
    have s8_6 : f (f x) < f x := by
      calc f (f x) = x := s8_2
        _ < f x := s8_1b
    -- 8.7. inequalities
    have s8_7 : f (f x) ≤ f x := by linarith only [s8_6]
    -- 8.8. inequalities, from 8.4, 8.5, 8.7
    have s8_8 : ¬ f x < f (f x) := by linarith only [s8_7]
    -- 8.9. def:set-builder u := f(x), from D2, H4, 8.1, 8.8
    exact ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun x : ℤ => ¬ x < f x)) (X := X) (u := f x))).mpr ⟨hH4 s8_1a, s8_8⟩
  set g : ℤ → ℤ := fun x : ℤ => f x with hD3
  -- 9. mun:function-into, from D3, 8
  have s9 : Set.MapsTo g L U := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := L) (Y := U) s8)
  -- 10. proof
  have s10 : ∀ s ∈ L, ∀ t ∈ L, g s = g t → s = t := by
    intro s hK2
    intro t hK3
    intro hK4
    -- 10.1. mun:in-subset, from K2, 3
    have s10_1 : s ∈ X := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := L) (Y := X) (u := s) s3 hK2)
    -- 10.2. mun:in-subset, from K3, 3
    have s10_2 : t ∈ X := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := L) (Y := X) (u := t) s3 hK3)
    -- 10.3. D3, from K2
    have s10_3 : g s = f s := by simp (disch := omega) only [hD3]
    -- 10.4. D3, from K3
    have s10_4 : g t = f t := by simp (disch := omega) only [hD3]
    -- 10.5. calculation
    have s10_5 : f s = f t := by
      calc f s = g s := s10_3.symm
        _ = g t := hK4
        _ = f t := s10_4
    -- 10.6. calculation
    calc s = f (f s) := by exact (hH5 s s10_1).symm
      _ = f (f t) := by (have h := congrArg (fun u : ℤ => f u) s10_5; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = t := by exact (hH5 t s10_2)
  -- 11. def:one-to-one, from 9, 10
  have s11 : Set.MapsTo g L U ∧ Set.InjOn g L := ((Parley.Items.Stdlib.Functions.def_one_to_one (X := L) (Y := U) (f := g) s9)).mpr ⟨s9, s10⟩
  -- 12. proof
  have s12 : ∀ u ∈ U, ∃ x ∈ L, u = g x := by
    intro u hK5
    -- 12.1. def:set-builder, from D2, K5
    have s12_1a : u ∈ X := by
      try simp only [hD2] at ⊢
      try push_cast at ⊢
      exact (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun x : ℤ => ¬ x < f x)) (X := X) (u := u))).mp hK5).1
    have s12_1b : ¬ u < f u := by
      try simp only [hD2] at ⊢
      try push_cast at ⊢
      have hI : ¬ u < f u := by parley_instance ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun x : ℤ => ¬ x < f x)) (X := X) (u := u))).mp hK5).2)
      exact hI
    -- 12.2. instantiate x := u in H5, from 12.1
    have s12_2 : f (f u) = u := by exact (hH5 u s12_1a)
    -- 12.3. instantiate x := u in H6, from 12.1
    have s12_3 : f u ≠ u := by exact (hH6 u s12_1a)
    -- 12.4. inequalities, from 12.1, 12.3
    have s12_4 : f u < u := Or.elim (Ne.lt_or_gt s12_3) (fun h1 => by linarith only [s12_1b, h1]) (fun h1 => by linarith only [s12_1b, h1])
    -- 12.5. calculation
    have s12_5 : f u < f (f u) := by
      calc f u < u := s12_4
        _ = f (f u) := s12_2.symm
    -- 12.6. def:set-builder u := f(u), from D1, H4, 12.1, 12.5
    have s12_6 : f u ∈ L := ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun x : ℤ => x < f x)) (X := X) (u := f u))).mpr ⟨hH4 s12_1a, s12_5⟩
    -- 12.7. D3, from 12.6
    have s12_7 : g (f u) = f (f u) := by simp (disch := omega) only [hD3]
    -- 12.8. calculation
    have s12_8 : u = g (f u) := by
      calc u = f (f u) := s12_2.symm
        _ = g (f u) := s12_7.symm
    -- 12.9. exhibit, from 12.6, 12.8
    exact ⟨f u, s12_6, s12_8⟩
  -- 13. def:onto, from 9, 12
  have s13 : Set.MapsTo g L U ∧ Set.SurjOn g L U := ((Parley.Items.Stdlib.Functions.def_onto (X := L) (Y := U) (f := g) s9)).mpr ⟨s9, s12⟩
  -- 14. def:one-to-one-onto, from 11, 13
  have s14 : Set.MapsTo g L U ∧ Set.InjOn g L ∧ Set.SurjOn g L U := ((Parley.Items.Stdlib.Functions.def_one_to_one_onto (X := L) (Y := U) (f := g) s11.1)).mpr ⟨s11, s13⟩
  -- 15. mun:product-reindex, from D3, 5, 7, 14
  have s15 : (∏ᶠ x ∈ U, (x : ℤ)) = (∏ᶠ x ∈ L, (f x : ℤ)) := by
    have hI : (∏ᶠ z ∈ U, (z : ℤ)) = (∏ᶠ y ∈ L, (g y : ℤ)) := by parley_instance ((Parley.Items.Stdlib.Sums.mun_product_reindex (t := (fun x : ℤ => x)) (Y := L) (Z := U) (g := g) s5 s14))
    exact hI
  -- 16. mun:int-real m := f(x)
  have s16 : ∀ x ∈ L, True := by intro x h_x; (trivial)
  -- 17. proof
  have s17 : ∀ x ∈ L, x * f x ≡ (1 : ℤ) [ZMOD n] := by
    intro x hK6
    -- 17.1. mun:in-subset, from K6, 3
    have s17_1 : x ∈ X := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := L) (Y := X) (u := x) s3 hK6)
    -- 17.2. instantiate x := x in H7, from 17.1
    exact (hH7 x s17_1)
  -- 18. proof
  have s18 : ∀ x ∈ L, True := by
    intro x hK7
    -- 18.1. mun:in-subset, from K7, 6
    -- 18.2. mun:in-subset, from D3, K7, 7, 9
    -- 18.3. membership, from 18.1, 18.2
    exact trivial
  -- 19. thm:product-congruent-termwise, from 5, 17, 18
  have s19 : (∏ᶠ x ∈ L, (x * f x : ℤ)) ≡ (∏ᶠ x ∈ L, (1 : ℤ)) [ZMOD n] := by exact (Parley.Items.Stdlib.Divisibility.thm_product_congruent_termwise (t := (fun x : ℤ => x * f x)) (u := (fun x : ℤ => (1 : ℤ))) (X := L) s5 (n := n) hH3 s17)
  -- 20. substitute
  have s20 : (∏ᶠ x ∈ L, (x * f x : ℤ)) ≡ (1 : ℤ) [ZMOD n] := by
    have c1 : (∏ᶠ x ∈ L, (1 : ℤ)) = 1 := by exact (Parley.Items.Stdlib.Sums.mun_product_of_ones (X := L) s5)
    have row1 : (∏ᶠ x ∈ L, (x * f x : ℤ)) ≡ (1 : ℤ) [ZMOD n] := by (have h := Eq.subst (motive := (fun t : ℤ => (∏ᶠ x ∈ L, (x * f x : ℤ)) ≡ t [ZMOD n])) c1 s19; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact row1
  -- 21. calculation
  have s21 : (∏ᶠ x ∈ X, (x : ℤ)) = (∏ᶠ x ∈ L, (x * f x : ℤ)) := by
    calc (∏ᶠ x ∈ X, (x : ℤ)) = (∏ᶠ x ∈ L, (x : ℤ)) * (∏ᶠ x ∈ U, (x : ℤ)) := by
          have hI : (∏ᶠ a ∈ X, (a : ℤ)) = (∏ᶠ a ∈ L, (a : ℤ)) * (∏ᶠ a ∈ U, (a : ℤ)) := by parley_instance ((Parley.Items.Stdlib.Sums.mun_product_split (t := (fun x : ℤ => x)) (X := X) (Y := L) (Z := U) hH2 s1 s2))
          exact hI
      _ = (∏ᶠ x ∈ L, (x : ℤ)) * (∏ᶠ x ∈ L, (f x : ℤ)) := by (have h := congrArg (fun t : ℤ => (∏ᶠ x ∈ L, (x : ℤ)) * t) s15; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = (∏ᶠ x ∈ L, (x * f x : ℤ)) := by linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_product_of_products (t := (fun x : ℤ => x)) (u := f) (X := L) s5).symm
  -- 22. substitute ∏(x ∈ X) x = ∏(x ∈ L) x·f(x) (line 21) into line 20
  (have h := Eq.subst (motive := (fun t : ℤ => t ≡ (1 : ℤ) [ZMOD n])) s21.symm s20; push_cast at h ⊢; all_goals exact_mod_cast h)

end Parley.Proofs.Wiedijk.Wilson.PairedProduct
