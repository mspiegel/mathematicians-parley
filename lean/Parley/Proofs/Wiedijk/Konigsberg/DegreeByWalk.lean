module

public import Graphs
public import Sets
public import Batteries.Util.ExtendedBinder
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Graphs
public import Parley.Items.Stdlib.Sets
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/wiedijk/konigsberg.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Konigsberg.DegreeByWalk

theorem degree_by_walk {α β : Type*} [Nonempty α] [Nonempty β] (V : Set α) (E : Set β) (G : β → Sym2 α) [LeanBridges.Graphs.Multigraph V E G] (n : ℤ) (hH2 : 0 ≤ n) (e : ℤ → β) (hH3 : Set.MapsTo e (Set.Icc (1 : ℤ) n : Set ℤ) E) (hH4 : Set.MapsTo e (Set.Icc (1 : ℤ) n : Set ℤ) E ∧ Set.InjOn e (Set.Icc (1 : ℤ) n : Set ℤ)) (hH5 : ∀ a ∈ E, ∃ i : ℤ, i ∈ Finset.Icc 1 n ∧ a = e i) (x : α) (hH6 : x ∈ V) :
    ({a ∈ E | x ∈ G a}.ncard : ℤ) = ({i ∈ (Set.Icc (1 : ℤ) n : Set ℤ) | x ∈ G (e i)}.ncard : ℤ) := by
  set S : Set ℤ := {i ∈ (Set.Icc (1 : ℤ) n : Set ℤ) | x ∈ G (e i)} with hD1
  have hD1_finite : S.Finite := by rw [hD1]; exact (Set.finite_Icc _ _).subset (fun _ h => h.1)
  set T : Set β := {a ∈ E | x ∈ G a} with hD2
  have hD2_finite : T.Finite := by rw [hD2]; exact (LeanBridges.Sets.finite_of_covered_by_range _ _ _ hH5).subset (fun _ h => h.1)
  set g : ℤ → β := fun i : ℤ => e i with hD3
  -- 1. proof
  have s1 : ∀ i ∈ S, g i ∈ T := by
    intro i hK1
    -- 1.1. def:set-builder u := i, from D1, K1
    have s1_1a : i ∈ Finset.Icc (1 : ℤ) n := by
      have hI : i ∈ Finset.Icc (1 : ℤ) n := by (have h := ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun i : ℤ => x ∈ G (e i))) (X := (Set.Icc (1 : ℤ) n : Set ℤ)) (u := i))).mp hK1).1); simp only [Finset.mem_Icc]; exact h)
      exact hI
    have s1_1b : x ∈ G (e i) := by
      have hI : x ∈ G (e i) := by exact ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun i : ℤ => x ∈ G (e i))) (X := (Set.Icc (1 : ℤ) n : Set ℤ)) (u := i))).mp hK1).2)
      exact hI
    -- 1.2. mun:function-value, from 1.1
    have s1_2 : e i ∈ E := by exact (Parley.Items.Stdlib.Functions.mun_function_value (D := (Set.Icc (1 : ℤ) n : Set ℤ)) (E := E) (f := e) (x := i) (by simpa only [Finset.mem_Icc, Set.mem_Icc] using s1_1a) hH3)
    -- 1.3. def:set-builder u := e(i), from D2, 1.1, 1.2
    have s1_3 : e i ∈ T := ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun a : β => x ∈ G a)) (X := E) (u := e i))).mpr ⟨s1_2, s1_1b⟩
    -- 1.4. D3, from K1
    have s1_4 : g i = e i := by simp (disch := omega) only [hD3]
    -- 1.5. substitute g(i) = e(i) (line 1.4) into line 1.3
    exact Eq.subst (motive := (fun t : β => t ∈ T)) s1_4.symm s1_3
  -- 2. mun:function-into, from 1
  have s2 : Set.MapsTo g S T := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := S) (Y := T) (by exact_mod_cast s1))
  -- 3. def:one-to-one, from H4
  have s3 : ∀ s : ℤ, s ∈ Finset.Icc 1 n → (∀ t : ℤ, t ∈ Finset.Icc 1 n → e s = e t → s = t) := by
    have hI : ∀ s : ℤ, s ∈ Finset.Icc 1 n → (∀ t : ℤ, t ∈ Finset.Icc 1 n → e s = e t → s = t) := by (have h := ((((Parley.Items.Stdlib.Functions.def_one_to_one (X := (Set.Icc (1 : ℤ) n : Set ℤ)) (Y := E) (f := e) hH4.1)).mp hH4).2); simp only [Finset.mem_Icc]; exact h)
    exact hI
  -- 4. proof
  have s4 : ∀ s ∈ S, ∀ t ∈ S, g s = g t → s = t := by
    intro s hK2
    intro t hK3
    intro hK4
    -- 4.1. def:set-builder u := s, from D1, K2
    have s4_1a : s ∈ Finset.Icc (1 : ℤ) n := by
      have hI : s ∈ Finset.Icc (1 : ℤ) n := by (have h := ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun i : ℤ => x ∈ G (e i))) (X := (Set.Icc (1 : ℤ) n : Set ℤ)) (u := s))).mp hK2).1); simp only [Finset.mem_Icc]; exact h)
      exact hI
    have s4_1b : x ∈ G (e s) := by
      have hI : x ∈ G (e s) := by exact ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun i : ℤ => x ∈ G (e i))) (X := (Set.Icc (1 : ℤ) n : Set ℤ)) (u := s))).mp hK2).2)
      exact hI
    -- 4.2. def:set-builder u := t, from D1, K3
    have s4_2a : t ∈ Finset.Icc (1 : ℤ) n := by
      have hI : t ∈ Finset.Icc (1 : ℤ) n := by (have h := ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun i : ℤ => x ∈ G (e i))) (X := (Set.Icc (1 : ℤ) n : Set ℤ)) (u := t))).mp hK3).1); simp only [Finset.mem_Icc]; exact h)
      exact hI
    have s4_2b : x ∈ G (e t) := by
      have hI : x ∈ G (e t) := by exact ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun i : ℤ => x ∈ G (e i))) (X := (Set.Icc (1 : ℤ) n : Set ℤ)) (u := t))).mp hK3).2)
      exact hI
    -- 4.3. D3, from K2
    have s4_3 : g s = e s := by simp (disch := omega) only [hD3]
    -- 4.4. D3, from K3
    have s4_4 : g t = e t := by simp (disch := omega) only [hD3]
    -- 4.5. calculation
    have s4_5 : e s = e t := by
      calc e s = g s := s4_3.symm
        _ = g t := hK4
        _ = e t := s4_4
    -- 4.6. instantiate s := s, t := t in line 3, from 4.1, 4.2, 4.5
    exact (s3 s s4_1a t s4_2a s4_5)
  -- 5. def:one-to-one, from 2, 4
  have s5 : Set.MapsTo g S T ∧ Set.InjOn g S := ((Parley.Items.Stdlib.Functions.def_one_to_one (X := S) (Y := T) (f := g) s2)).mpr ⟨s2, s4⟩
  -- 6. proof
  have s6 : ∀ a ∈ T, ∃ i ∈ S, a = g i := by
    intro a hK5
    -- 6.1. def:set-builder u := a, from D2, K5
    have s6_1a : a ∈ E := by exact (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun a : β => x ∈ G a)) (X := E) (u := a))).mp hK5).1
    have s6_1b : x ∈ G a := by
      have hI : x ∈ G a := by exact ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun a : β => x ∈ G a)) (X := E) (u := a))).mp hK5).2)
      exact hI
    -- 6.2. instantiate a := a in H5, from 6.1
    have s6_2 : ∃ i : ℤ, i ∈ Finset.Icc 1 n ∧ a = e i := by exact (hH5 a s6_1a)
    -- 6.3. obtain i from line 6.2
    obtain ⟨i, s6_3a, s6_3b⟩ := s6_2
    -- 6.4. substitute a = e(i) (line 6.3) into line 6.1
    have s6_4 : x ∈ G (e i) := Eq.subst (motive := (fun t : β => x ∈ G t)) s6_3b s6_1b
    -- 6.5. def:set-builder u := i, from D1, 6.3, 6.4
    have s6_5 : i ∈ S := ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun i : ℤ => x ∈ G (e i))) (X := (Set.Icc (1 : ℤ) n : Set ℤ)) (u := i))).mpr ⟨by simpa only [Finset.mem_Icc, Set.mem_Icc] using s6_3a, s6_4⟩
    -- 6.6. D3, from 6.5
    have s6_6 : g i = e i := by simp (disch := omega) only [hD3]
    -- 6.7. calculation
    have s6_7 : a = g i := by
      calc a = e i := s6_3b
        _ = g i := s6_6.symm
    -- 6.8. exhibit, from 6.5, 6.7
    exact ⟨i, s6_5, s6_7⟩
  -- 7. def:bijection, from D1
  have r143_1 : Set.MapsTo g S T ∧ Set.SurjOn g S T := ((Parley.Items.Stdlib.Functions.def_onto (X := S) (Y := T) (f := g) s2)).mpr ⟨s2, by intro y h_y; exact_mod_cast s6 y h_y⟩
  have r143_2 : Set.MapsTo g S T ∧ Set.InjOn g S ∧ Set.SurjOn g S T := ((Parley.Items.Stdlib.Functions.def_one_to_one_onto (X := S) (Y := T) (f := g) s5.1)).mpr ⟨s5, r143_1⟩
  have s7 : ∃ g : ℤ → β, Set.BijOn g S T := by
    have hI : ∃ g : ℤ → β, Set.BijOn g S T := by exact ((Parley.Items.Stdlib.Functions.def_bijection (X := S) (Y := T) (f := g) r143_2))
    exact hI
  -- 8. calculation
  have r148_1 : S ⊆ (Set.Icc (1 : ℤ) n : Set ℤ) := by
    simp only [hD1] at ⊢
    push_cast at ⊢
    (have h := (Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun i : ℤ => x ∈ G (e i))) (X := (Set.Icc (1 : ℤ) n : Set ℤ))); push_cast at h; exact h)
  have r148_2 : (Set.Icc (1 : ℤ) n : Set ℤ).Finite := by exact (Parley.Items.Stdlib.Sums.mun_range_finite (a := (1 : ℤ)) (b := n))
  have r148_3 : S.Finite := by exact (Parley.Items.Stdlib.Counting.mun_finite_part (X := (Set.Icc (1 : ℤ) n : Set ℤ)) (Y := S) r148_2 r148_1)
  calc ({a ∈ E | x ∈ G a}.ncard : ℤ) = (T.ncard : ℤ) := by simp only [hD2] at ⊢
    _ = (S.ncard : ℤ) := by (have h := (Parley.Items.Stdlib.Counting.mun_card_equal (X := S) (Y := T) r148_3 s7); simp only [← Set.Finite.cast_ncard_eq ((hD2_finite : (T : Set β).Finite)), ← Set.Finite.cast_ncard_eq ((hD1_finite : (S : Set ℤ).Finite))] at h ⊢; exact_mod_cast h.symm)
    _ = ({i ∈ (Set.Icc (1 : ℤ) n : Set ℤ) | x ∈ G (e i)}.ncard : ℤ) := by simp (disch := omega) only [hD1]

end Parley.Proofs.Wiedijk.Konigsberg.DegreeByWalk
