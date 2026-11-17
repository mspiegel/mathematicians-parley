module

public import Functions
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Operations
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
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Wiedijk.SchroederBernstein.FixedPart

/-! Written from proofs/wiedijk/schroeder-bernstein.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.SchroederBernstein.SchroederBernstein

theorem schroeder_bernstein {α β : Type*} [Nonempty α] [Nonempty β] (A : Set α) (B : Set β) (f : α → β) (hH3 : Set.MapsTo f A B ∧ Set.InjOn f A) (g : β → α) (hH4 : Set.MapsTo g B A ∧ Set.InjOn g B) :
    (∃ g : α → β, Set.BijOn g A B) := by
  -- 1. def:one-to-one, from H3
  have s1 : ∀ s ∈ A, ∀ t ∈ A, f s = f t → s = t := by exact (((Parley.Items.Stdlib.Functions.def_one_to_one (X := A) (Y := B) (f := f) hH3.1)).mp hH3).2
  -- 2. obtain C: thm:fixed-part
  obtain ⟨C, s2a, s2b⟩ := (Parley.Proofs.Wiedijk.SchroederBernstein.FixedPart.fixed_part (A := A) (B := B) (f := f) hH3.1 (g := g) hH4.1)
  set R : Set β := f '' (A ∩ C) with hD1
  set h : α → β := fun x : α => @ite _ (x ∈ C) (Classical.propDecidable (x ∈ C)) (f x) (LeanBridges.Functions.inverse g B x) with hD2
  -- 3. proof
  have s3 : ∀ t ∈ A \ C, h t ∈ B \ R ∧ g (h t) = t := by
    intro t hK1
    -- 3.1. def:difference, from K1
    have s3_1a : t ∈ A := by exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp hK1).1
    have s3_1b : ¬ t ∈ C := by exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp hK1).2
    -- 3.2. mun:equal-subset, from D1, 2
    have s3_2 : A \ C ⊆ g '' (B ∩ (B \ R)) := by
      simp only [hD1] at ⊢
      push_cast at ⊢
      exact (Parley.Items.Stdlib.Sets.mun_equal_subset (X := A \ C) (Y := g '' (B ∩ (B \ f '' (A ∩ C)))) s2b.symm)
    -- 3.3. mun:in-subset, from K1, 3.2
    have s3_3 : t ∈ g '' (B ∩ (B \ R)) := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := A \ C) (Y := g '' (B ∩ (B \ R))) (u := t) s3_2 hK1)
    -- 3.4. obtain y: def:image f := g, u := t, Y := B ∖ R, from 3.3
    have r187_1 : B \ R ⊆ B := by exact (Parley.Items.Stdlib.Sets.mun_difference_subset (X := B) (Y := R))
    obtain ⟨y, s3_4a, s3_4b⟩ := ((Parley.Items.Stdlib.Functions.def_image (X := B) (Y := B \ R) (f := g) (u := t) (W := A) r187_1 hH4.1)).mp s3_3
    -- 3.5. def:difference, from 3.4
    have s3_5 : y ∈ B := by exact (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := R) (u := y))).mp s3_4a).1
    -- 3.6. D2, from 3.1
    have s3_6 : h t = LeanBridges.Functions.inverse g B t := by simp (disch := omega) only [hD2, if_neg s3_1b]
    -- 3.7. calculation
    have s3_7 : h t = y := by
      calc h t = LeanBridges.Functions.inverse g B t := s3_6
        _ = LeanBridges.Functions.inverse g B (g y) := congrArg (fun u : α => LeanBridges.Functions.inverse g B u) s3_4b
        _ = y := by exact (Parley.Items.Stdlib.Functions.mun_inverse_value (X := A) (Y := B) (g := g) (y := y) hH4 s3_5)
    -- 3.8. substitute h(t) = y (line 3.7) into line 3.4
    have s3_8 : h t ∈ B \ R := Eq.subst (motive := (fun u : β => u ∈ B \ R)) s3_7.symm s3_4a
    -- 3.9. calculation
    have s3_9 : g (h t) = t := by
      calc g (h t) = g y := congrArg (fun u : β => g u) s3_7
        _ = t := s3_4b.symm
    -- 3.10. join 3.8, 3.9
    have s3_10a : h t ∈ B \ R := s3_8
    have s3_10b : g (h t) = t := s3_9
    exact ⟨s3_10a, s3_10b⟩
  -- 4. proof
  have s4 : ∀ u ∈ C, ∀ v ∈ A \ C, ¬ h u = h v := by
    intro u hK2
    intro v hK3
    intro hS1
    -- 4.1. D2, from K2
    have r221_1 : u ∈ A := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := C) (Y := A) (u := u) s2a hK2)
    have s4_1 : h u = f u := by simp (disch := omega) only [hD2, if_pos hK2]
    -- 4.2. mun:value-in-image, from D1, K2
    have r225_1 : C ⊆ A := by exact s2a
    have s4_2 : f u ∈ R := by
      simp only [hD1] at ⊢
      push_cast at ⊢
      exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := C) (f := f) (s := u) (W := B) r225_1 hK2 hH3.1)
    -- 4.3. calculation
    have s4_3 : h v = f u := by
      calc h v = h u := hS1.symm
        _ = f u := s4_1
    -- 4.4. substitute h(v) = f(u) (line 4.3) into line 4.2
    have s4_4 : h v ∈ R := Eq.subst (motive := (fun t : β => t ∈ R)) s4_3.symm s4_2
    -- 4.5. def:difference, from 3
    have s4_5 : ¬ h v ∈ R := by exact (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := R) (u := h v))).mp (s3 v hK3).1).2
    exact s4_5 s4_4
  -- 5. proof
  have s5 : ∀ s ∈ A, h s ∈ B := by
    intro s hK4
    -- 5.1. axi:excluded-middle P := s ∈ C
    have s5_1 : s ∈ C ∨ ¬ s ∈ C := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := s ∈ C))
    -- 5.2. cases, from 5.1
    rcases s5_1 with hC1 | hC2
    · skip
      -- 5.2.1. D2, from C1
      have r253_1 : s ∈ A := by exact hK4
      have s5_2_1 : h s = f s := by simp (disch := omega) only [hD2, if_pos hC1]
      -- 5.2.2. mun:function-value x := s, from K4
      have s5_2_2 : f s ∈ B := by exact (Parley.Items.Stdlib.Functions.mun_function_value (D := A) (E := B) (f := f) (x := s) hK4 hH3.1)
      -- 5.2.3. substitute h(s) = f(s) (line 5.2.1) into line 5.2.2
      exact Eq.subst (motive := (fun t : β => t ∈ B)) s5_2_1.symm s5_2_2
    · skip
      -- 5.2.4. def:difference, from C2, K4
      have s5_2_4 : s ∈ A \ C := ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := s))).mpr ⟨hK4, hC2⟩
      -- 5.2.5. instantiate t := s in line 3, from 5.2.4
      have s5_2_5a : h s ∈ B \ R := by exact (s3 s s5_2_4).1
      have s5_2_5b : g (h s) = s := by exact (s3 s s5_2_4).2
      -- 5.2.6. def:difference, from 5.2.5
      exact (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := R) (u := h s))).mp s5_2_5a).1
  -- 6. mun:function-into, from 5
  have s6 : Set.MapsTo h A B := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := h) (X := A) (Y := B) s5)
  -- 7. proof
  have s7 : ∀ s ∈ A, ∀ t ∈ A, h s = h t → s = t := by
    intro s hK5
    intro t hK6
    intro hA1
    -- 7.1. axi:excluded-middle P := s ∈ C
    have s7_1 : s ∈ C ∨ ¬ s ∈ C := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := s ∈ C))
    -- 7.2. axi:excluded-middle P := t ∈ C
    have s7_2 : t ∈ C ∨ ¬ t ∈ C := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := t ∈ C))
    -- 7.3. cases, from 7.1
    rcases s7_1 with hC3 | hC6
    · skip
      -- 7.3.1. cases, from 7.2
      rcases s7_2 with hC4 | hC5
      · skip
        -- 7.3.1.1. D2, from C3
        have r303_1 : s ∈ A := by exact hK5
        have s7_3_1_1 : h s = f s := by simp (disch := omega) only [hD2, if_pos hC3]
        -- 7.3.1.2. D2, from C4
        have r307_1 : t ∈ A := by exact hK6
        have s7_3_1_2 : h t = f t := by simp (disch := omega) only [hD2, if_pos hC4]
        -- 7.3.1.3. calculation
        have s7_3_1_3 : f s = f t := by
          calc f s = h s := s7_3_1_1.symm
            _ = h t := hA1
            _ = f t := s7_3_1_2
        -- 7.3.1.4. instantiate s := s, t := t in line 1, from K5, K6, 7.3.1.3
        exact (s1 s hK5 t hK6 s7_3_1_3)
      · skip
        -- 7.3.1.5. def:difference, from C5, K6
        have s7_3_1_5 : t ∈ A \ C := ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mpr ⟨hK6, hC5⟩
        -- 7.3.1.6. instantiate u := s, v := t in line 4, from C3, 7.3.1.5
        have s7_3_1_6 : ¬ h s = h t := by exact (s4 s hC3 t s7_3_1_5)
        exact absurd hA1 s7_3_1_6
    · skip
      -- 7.3.2. def:difference, from C6, K5
      have s7_3_2 : s ∈ A \ C := ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := s))).mpr ⟨hK5, hC6⟩
      -- 7.3.3. instantiate t := s in line 3, from 7.3.2
      have s7_3_3a : h s ∈ B \ R := by exact (s3 s s7_3_2).1
      have s7_3_3b : g (h s) = s := by exact (s3 s s7_3_2).2
      -- 7.3.4. cases, from 7.2
      rcases s7_2 with hC7 | hC8
      · skip
        -- 7.3.4.1. instantiate u := t, v := s in line 4, from C7, 7.3.2
        have s7_3_4_1 : ¬ h s = h t := by exact (s4 t hC7 s s7_3_2).symm
        exact absurd hA1 s7_3_4_1
      · skip
        -- 7.3.4.2. def:difference, from C8, K6
        have s7_3_4_2 : t ∈ A \ C := ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mpr ⟨hK6, hC8⟩
        -- 7.3.4.3. instantiate t := t in line 3, from 7.3.4.2
        have s7_3_4_3a : h t ∈ B \ R := by exact (s3 t s7_3_4_2).1
        have s7_3_4_3b : g (h t) = t := by exact (s3 t s7_3_4_2).2
        -- 7.3.4.4. calculation
        calc s = g (h s) := s7_3_3b.symm
          _ = g (h t) := congrArg (fun u : β => g u) hA1
          _ = t := s7_3_4_3b
  -- 8. proof
  have s8 : ∀ b ∈ B, ∃ s ∈ A, b = h s := by
    intro b hK7
    -- 8.1. axi:excluded-middle P := b ∈ R
    have s8_1 : b ∈ R ∨ ¬ b ∈ R := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := b ∈ R))
    -- 8.2. cases, from 8.1
    rcases s8_1 with hC9 | hC10
    · skip
      -- 8.2.1. obtain x: def:image u := b, Y := C, from C9, D1
      have r375_1 : C ⊆ A := by exact s2a
      obtain ⟨x, s8_2_1a, s8_2_1b⟩ := ((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := C) (f := f) (u := b) (W := Set.univ) r375_1 (Set.mapsTo_univ _ _))).mp hC9
      -- 8.2.2. mun:in-subset, from 2, 8.2.1
      have s8_2_2 : x ∈ A := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := C) (Y := A) (u := x) s2a s8_2_1a)
      -- 8.2.3. D2, from 8.2.1
      have r382_1 : x ∈ A := by exact s8_2_2
      have s8_2_3 : h x = f x := by simp (disch := omega) only [hD2, if_pos s8_2_1a]
      -- 8.2.4. calculation
      have s8_2_4 : b = h x := by
        calc b = f x := s8_2_1b
          _ = h x := s8_2_3.symm
      -- 8.2.5. exhibit, from 8.2.2, 8.2.4
      exact ⟨x, s8_2_2, s8_2_4⟩
    · skip
      -- 8.2.6. def:difference, from C10, K7
      have s8_2_6 : b ∈ B \ R := ((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := R) (u := b))).mpr ⟨hK7, hC10⟩
      -- 8.2.7. mun:value-in-image f := g, from 8.2.6
      have r400_1 : B \ R ⊆ B := by exact (Parley.Items.Stdlib.Sets.mun_difference_subset (X := B) (Y := R))
      have s8_2_7 : g b ∈ g '' (B ∩ (B \ R)) := by exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := B) (Y := B \ R) (f := g) (s := b) (W := A) r400_1 s8_2_6 hH4.1)
      -- 8.2.8. mun:equal-subset, from D1, 2
      have s8_2_8 : g '' (B ∩ (B \ R)) ⊆ A \ C := by
        simp only [hD1] at ⊢
        push_cast at ⊢
        exact (Parley.Items.Stdlib.Sets.mun_equal_subset (X := g '' (B ∩ (B \ f '' (A ∩ C)))) (Y := A \ C) s2b)
      -- 8.2.9. mun:in-subset, from 8.2.7, 8.2.8
      have s8_2_9 : g b ∈ A \ C := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := g '' (B ∩ (B \ R))) (Y := A \ C) (u := g b) s8_2_8 s8_2_7)
      -- 8.2.10. def:difference, from 8.2.9
      have s8_2_10a : g b ∈ A := by exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := g b))).mp s8_2_9).1
      have s8_2_10b : ¬ g b ∈ C := by exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := g b))).mp s8_2_9).2
      -- 8.2.11. D2, from 8.2.10
      have s8_2_11 : h (g b) = LeanBridges.Functions.inverse g B (g b) := by simp (disch := omega) only [hD2, if_neg s8_2_10b]
      -- 8.2.12. calculation
      have s8_2_12 : b = h (g b) := by
        calc b = LeanBridges.Functions.inverse g B (g b) := (Parley.Items.Stdlib.Functions.mun_inverse_value (X := A) (Y := B) (g := g) (y := b) hH4 hK7).symm
          _ = h (g b) := s8_2_11.symm
      -- 8.2.13. exhibit, from 8.2.10, 8.2.12
      exact ⟨g b, s8_2_10a, s8_2_12⟩
  -- 9. def:one-to-one, from 6, 7
  have s9 : Set.MapsTo h A B ∧ Set.InjOn h A := ((Parley.Items.Stdlib.Functions.def_one_to_one (X := A) (Y := B) (f := h) s6)).mpr ⟨s6, s7⟩
  -- 10. def:bijection
  have r427_1 : Set.MapsTo h A B ∧ Set.SurjOn h A B := ((Parley.Items.Stdlib.Functions.def_onto (X := A) (Y := B) (f := h) s6)).mpr ⟨s6, s8⟩
  have r427_2 : Set.MapsTo h A B ∧ Set.InjOn h A ∧ Set.SurjOn h A B := ((Parley.Items.Stdlib.Functions.def_one_to_one_onto (X := A) (Y := B) (f := h) s9.1)).mpr ⟨s9, r427_1⟩
  exact (Parley.Items.Stdlib.Functions.def_bijection (X := A) (Y := B) (f := h) r427_2)

end Parley.Proofs.Wiedijk.SchroederBernstein.SchroederBernstein
