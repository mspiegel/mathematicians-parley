module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Linter.Style
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
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Groups
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/wiedijk/lagrange.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Lagrange.CosetSize

theorem coset_size {G : Type*} [Group G] (hH1 : (Set.univ : Set G).Finite) (H : Subgroup G) (g : G) (hH3 : g ∈ (Set.univ : Set G)) :
    ((g * ·) '' (H : Set G)).encard = (H : Set G).encard := by
  -- 1. mun:subgroup-within, from H2
  have s1 : (H : Set G) ⊆ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Groups.mun_subgroup_within (G := G) (H := H))
  -- 2. mun:finite-part, from H1, 1
  have s2 : (H : Set G).Finite := by exact (Parley.Items.Stdlib.Counting.mun_finite_part (X := (Set.univ : Set G)) (Y := (H : Set G)) hH1 s1)
  set t : G → G := fun c : G => g * c with hD1
  -- 3. proof
  have s3 : ∀ h ∈ (H : Set G), t h ∈ (g * ·) '' (H : Set G) := by
    intro h hK1
    -- 3.1. D1, from K1
    have s3_1 : t h = g * h := by simp (disch := omega) only [hD1]
    -- 3.2. def:coset u := t(h), from H2, H3, K1, 3.1
    exact ((Parley.Items.Stdlib.Groups.def_coset (G := G) (g := g) (u := t h) (H := H) (Set.mem_univ _))).mpr ⟨h, hK1, s3_1⟩
  -- 4. mun:function-into, from 3
  have s4 : Set.MapsTo t (H : Set G) ((g * ·) '' (H : Set G)) := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := t) (X := (H : Set G)) (Y := (g * ·) '' (H : Set G)) s3)
  -- 5. proof
  have s5 : ∀ s ∈ (H : Set G), ∀ r ∈ (H : Set G), t s = t r → s = r := by
    intro s hK2
    intro r hK3
    intro hA1
    -- 5.1. D1, from K2
    have s5_1 : t s = g * s := by simp (disch := omega) only [hD1]
    -- 5.2. D1, from K3
    have s5_2 : t r = g * r := by simp (disch := omega) only [hD1]
    -- 5.3. calculation
    have s5_3 : g * s = g * r := by
      calc g * s = t s := s5_1.symm
        _ = t r := hA1
        _ = g * r := s5_2
    -- 5.4. mun:in-subset, from K2, 1
    have s5_4 : s ∈ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := (H : Set G)) (Y := (Set.univ : Set G)) (u := s) s1 hK2)
    -- 5.5. mun:in-subset, from K3, 1
    have s5_5 : r ∈ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := (H : Set G)) (Y := (Set.univ : Set G)) (u := r) s1 hK3)
    -- 5.6. thm:group-cancel a := s, b := r, from H3, 5.3, 5.4, 5.5
    exact (Parley.Items.Stdlib.Groups.thm_group_cancel (G := G) (a := s) (b := r) (g := g) (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _) s5_3)
  -- 6. def:one-to-one, from 4, 5
  have s6 : Set.MapsTo t (H : Set G) ((g * ·) '' (H : Set G)) ∧ Set.InjOn t (H : Set G) := ((Parley.Items.Stdlib.Functions.def_one_to_one (X := (H : Set G)) (Y := (g * ·) '' (H : Set G)) (f := t) s4)).mpr ⟨s4, s5⟩
  -- 7. proof
  have s7 : ∀ u ∈ (g * ·) '' (H : Set G), ∃ h ∈ (H : Set G), u = t h := by
    intro u hK4
    -- 7.1. obtain h: def:coset, from H2, H3, K4
    obtain ⟨h, s7_1a, s7_1b⟩ := ((Parley.Items.Stdlib.Groups.def_coset (G := G) (g := g) (u := u) (H := H) (Set.mem_univ _))).mp hK4
    -- 7.2. D1, from 7.1
    have s7_2 : t h = g * h := by simp (disch := omega) only [hD1]
    -- 7.3. calculation
    have s7_3 : u = t h := by
      calc u = g * h := s7_1b
        _ = t h := s7_2.symm
    -- 7.4. exhibit, from 7.1, 7.3
    exact ⟨h, s7_1a, s7_3⟩
  -- 8. def:bijection
  have r255_1 : Set.MapsTo t (H : Set G) ((g * ·) '' (H : Set G)) ∧ Set.SurjOn t (H : Set G) ((g * ·) '' (H : Set G)) := ((Parley.Items.Stdlib.Functions.def_onto (X := (H : Set G)) (Y := (g * ·) '' (H : Set G)) (f := t) s4)).mpr ⟨s4, s7⟩
  have r255_2 : Set.MapsTo t (H : Set G) ((g * ·) '' (H : Set G)) ∧ Set.InjOn t (H : Set G) ∧ Set.SurjOn t (H : Set G) ((g * ·) '' (H : Set G)) := ((Parley.Items.Stdlib.Functions.def_one_to_one_onto (X := (H : Set G)) (Y := (g * ·) '' (H : Set G)) (f := t) s6.1)).mpr ⟨s6, r255_1⟩
  have s8 : ∃ h : G → G, Set.BijOn h (H : Set G) ((g * ·) '' (H : Set G)) := by exact (Parley.Items.Stdlib.Functions.def_bijection (X := (H : Set G)) (Y := (g * ·) '' (H : Set G)) (f := t) r255_2)
  -- 9. mun:card-equal X := H, Y := gH, from 2, 8
  have s9 : (((g * ·) '' (H : Set G)).ncard : ℤ) = ((H : Set G).ncard : ℤ) := by (have h := (Parley.Items.Stdlib.Counting.mun_card_equal (X := (H : Set G)) (Y := (g * ·) '' (H : Set G)) s2 s8); simp only [← Set.Finite.cast_ncard_eq (((s2).image _ : ((g * ·) '' (H : Set G) : Set G).Finite)), ← Set.Finite.cast_ncard_eq ((s2 : ((H : Set G) : Set G).Finite))] at h ⊢; exact_mod_cast h.symm)
  show ((g * ·) '' (H : Set G)).encard = (H : Set G).encard; exact by (have h := s9; simp only [← Set.Finite.cast_ncard_eq (((s2).image _ : ((g * ·) '' (H : Set G) : Set G).Finite)), ← Set.Finite.cast_ncard_eq ((s2 : ((H : Set G) : Set G).Finite))] at h ⊢; exact_mod_cast h)

end Parley.Proofs.Wiedijk.Lagrange.CosetSize
