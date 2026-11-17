module

public import Batteries.Util.ExtendedBinder
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
public import Mathlib.Order.SetNotation
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Groups
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Wiedijk.Lagrange.CosetMember
public import Parley.Proofs.Wiedijk.Lagrange.CosetOfMember
public import Parley.Proofs.Wiedijk.Lagrange.CosetSize
public import Parley.Proofs.Wiedijk.Lagrange.CosetWithin

/-! Written from proofs/wiedijk/lagrange.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Lagrange.Lagrange

theorem lagrange {G : Type*} [Group G] (hH1 : (Set.univ : Set G).Finite) (H : Subgroup G) :
    (∃ m : ℕ, (H : Set G).encard = (m : ℕ∞) ∧ (m : ℤ) ∣ ((Set.univ : Set G).ncard : ℤ)) := by
  set K : Set (Set G) := {X ∈ 𝒫 (Set.univ : Set G) | ∃ g ∈ (Set.univ : Set G), X = (g * ·) '' (H : Set G)} with hD1
  have hD1_finite : K.Finite := by rw [hD1]; exact ((hH1).powerset).subset (fun _ h => h.1)
  -- 1. mun:subgroup-within, from H2
  have s1 : (H : Set G) ⊆ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Groups.mun_subgroup_within (G := G) (H := H))
  -- 2. mun:finite-part, from H1, 1
  have s2 : (H : Set G).Finite := by exact (Parley.Items.Stdlib.Counting.mun_finite_part (X := (Set.univ : Set G)) (Y := (H : Set G)) hH1 s1)
  -- 3. def:part-builder, from D1
  have s3 : ∀ Y ∈ K, Y ⊆ (Set.univ : Set G) := by intro Y h_Y; (exact (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun X : Set G => ∃ g ∈ (Set.univ : Set G), X = (g * ·) '' (H : Set G))) (X := (Set.univ : Set G)) (u := Y))).mp h_Y).1)
  -- 4. mun:union-within, from 3
  have s4 : (⋃ Y ∈ K, Y) ⊆ (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Sets.mun_union_within (D := K) (Z := (Set.univ : Set G)) s3)
  -- 5. proof
  have s5 : ∀ g ∈ (Set.univ : Set G), g ∈ (⋃ Y ∈ K, Y) := by
    intro g hK1
    -- 5.1. thm:coset-within, from H2, K1
    have s5_1 : (g * ·) '' (H : Set G) ⊆ (Set.univ : Set G) := by exact (Parley.Proofs.Wiedijk.Lagrange.CosetWithin.coset_within (G := G) (H := H) (g := g) (Set.mem_univ _))
    -- 5.2. thm:coset-member, from H2, K1
    have s5_2 : g ∈ (g * ·) '' (H : Set G) := by exact (Parley.Proofs.Wiedijk.Lagrange.CosetMember.coset_member (G := G) (H := H) (g := g) (Set.mem_univ _))
    -- 5.3. exhibit, from K1
    have s5_3 : ∃ a ∈ (Set.univ : Set G), (g * ·) '' (H : Set G) = (a * ·) '' (H : Set G) := ⟨g, Set.mem_univ _, rfl⟩
    -- 5.4. def:part-builder u := gH, from D1, 5.1, 5.3
    have s5_4 : (g * ·) '' (H : Set G) ∈ K := ((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun X : Set G => ∃ g ∈ (Set.univ : Set G), X = (g * ·) '' (H : Set G))) (X := (Set.univ : Set G)) (u := (g * ·) '' (H : Set G)))).mpr ⟨s5_1, s5_3⟩
    -- 5.5. exhibit, from 5.2, 5.4
    have s5_5 : ∃ Y ∈ K, g ∈ Y := ⟨(g * ·) '' (H : Set G), s5_4, s5_2⟩
    -- 5.6. def:indexed-union u := g, from 5.5
    exact ((Parley.Items.Stdlib.Sets.def_indexed_union (D := K) (u := g))).mpr s5_5
  -- 6. def:subset, from 5
  have s6 : (Set.univ : Set G) ⊆ (⋃ Y ∈ K, Y) := ((Parley.Items.Stdlib.Sets.def_subset (X := (Set.univ : Set G)) (Y := ⋃ Y ∈ K, Y))).mpr s5
  -- 7. mun:subset-antisymmetric, from 4, 6
  have s7 : (⋃ Y ∈ K, Y) = (Set.univ : Set G) := by exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := ⋃ Y ∈ K, Y) (Y := (Set.univ : Set G)) s4 s6)
  -- 8. proof
  have s8 : ∀ Y ∈ K, ∀ Z ∈ K, ∀ x ∈ Y ∩ Z, Y = Z := by
    intro Y hK2
    intro Z hK3
    intro x hK4
    -- 8.1. obtain a: def:part-builder, from D1, K2
    obtain ⟨_, a, s8_1a, s8_1b⟩ := ((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun X : Set G => ∃ g ∈ (Set.univ : Set G), X = (g * ·) '' (H : Set G))) (X := (Set.univ : Set G)) (u := Y))).mp hK2
    -- 8.2. obtain b: def:part-builder, from D1, K3
    obtain ⟨_, b, s8_2a, s8_2b⟩ := ((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun X : Set G => ∃ g ∈ (Set.univ : Set G), X = (g * ·) '' (H : Set G))) (X := (Set.univ : Set G)) (u := Z))).mp hK3
    -- 8.3. def:intersection, from K4
    have s8_3a : x ∈ Y := by exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := Y) (Z := Z) (u := x))).mp hK4).1
    have s8_3b : x ∈ Z := by exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := Y) (Z := Z) (u := x))).mp hK4).2
    -- 8.4. substitute Y = aH (line 8.1) into line 8.3
    have s8_4 : x ∈ (a * ·) '' (H : Set G) := Eq.subst (motive := (fun t : Set G => x ∈ t)) s8_1b s8_3a
    -- 8.5. substitute Z = bH (line 8.2) into line 8.3
    have s8_5 : x ∈ (b * ·) '' (H : Set G) := Eq.subst (motive := (fun t : Set G => x ∈ t)) s8_2b s8_3b
    -- 8.6. calculation
    calc Y = (a * ·) '' (H : Set G) := s8_1b
      _ = (x * ·) '' (H : Set G) := by exact (Parley.Proofs.Wiedijk.Lagrange.CosetOfMember.coset_of_member (G := G) (H := H) (a := a) (Set.mem_univ _) (x := x) s8_4).symm
      _ = (b * ·) '' (H : Set G) := by exact (Parley.Proofs.Wiedijk.Lagrange.CosetOfMember.coset_of_member (G := G) (H := H) (a := b) (Set.mem_univ _) (x := x) s8_5)
      _ = Z := s8_2b.symm
  -- 9. proof
  have s9 : ∀ Y ∈ K, (Y.ncard : ℤ) = ((H : Set G).ncard : ℤ) := by
    intro Y hK5
    -- 9.1. obtain a: def:part-builder, from D1, K5
    obtain ⟨_, a, s9_1a, s9_1b⟩ := ((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun X : Set G => ∃ g ∈ (Set.univ : Set G), X = (g * ·) '' (H : Set G))) (X := (Set.univ : Set G)) (u := Y))).mp hK5
    -- 9.2. calculation
    calc (Y.ncard : ℤ) = (((a * ·) '' (H : Set G)).ncard : ℤ) := congrArg (fun t : Set G => (t.ncard : ℤ)) s9_1b
      _ = ((H : Set G).ncard : ℤ) := by (have h := (Parley.Proofs.Wiedijk.Lagrange.CosetSize.coset_size (G := G) hH1 (H := H) (g := a) (Set.mem_univ _)); simp only [← Set.Finite.cast_ncard_eq (((s2).image _ : ((a * ·) '' (H : Set G) : Set G).Finite)), ← Set.Finite.cast_ncard_eq ((s2 : ((H : Set G) : Set G).Finite))] at h ⊢; exact_mod_cast h)
  -- 10. mun:partition-count A := G, m := |H|, from H1, 7, 8, 9
  have r355_1 : 0 ≤ ((H : Set G).ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := (H : Set G)) s2)
  have s10 : ((Set.univ : Set G).ncard : ℤ) = (K.ncard : ℤ) * ((H : Set G).ncard : ℤ) := by (have h := (Parley.Items.Stdlib.Counting.mun_partition_count (A := (Set.univ : Set G)) (K := K) (m := ((H : Set G).ncard : ℤ)) r355_1 hH1 s7 s8 (fun Y h_mem => by simp only [← Set.Finite.cast_ncard_eq ((((hH1)).subset (h_mem).1 : (Y : Set G).Finite)), Int.toNat_natCast]; exact_mod_cast s9 Y h_mem)); simp only [← Set.Finite.cast_ncard_eq ((hH1 : ((Set.univ : Set G) : Set G).Finite)), ← Set.Finite.cast_ncard_eq ((hD1_finite : (K : Set (Set G)).Finite)), ← Set.Finite.cast_ncard_eq ((s2 : ((H : Set G) : Set G).Finite))] at h ⊢; exact_mod_cast h)
  -- 11. mun:parts-finite A := G, from H1, 3
  have s11 : K.Finite := by exact (Parley.Items.Stdlib.Counting.mun_parts_finite (A := (Set.univ : Set G)) (K := K) hH1 s3)
  -- 12. algebra, from 10
  have r362_1 : 0 ≤ (K.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := K) s11)
  have r362_2 : 0 ≤ ((H : Set G).ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := (H : Set G)) s2)
  have s12 : ((Set.univ : Set G).ncard : ℤ) = ((H : Set G).ncard : ℤ) * (K.ncard : ℤ) := by linear_combination s10
  -- 13. def:divides d := |H|, n := |G|, from 12
  have r367_1 : 0 ≤ ((H : Set G).ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := (H : Set G)) s2)
  have r367_2 : 0 ≤ (K.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := K) s11)
  have r367_3 : 0 ≤ ((Set.univ : Set G).ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := (Set.univ : Set G)) hH1)
  have s13 : ((H : Set G).ncard : ℤ) ∣ ((Set.univ : Set G).ncard : ℤ) := ((Parley.Items.Stdlib.Divisibility.def_divides (d := ((H : Set G).ncard : ℤ)) (n := ((Set.univ : Set G).ncard : ℤ)))).mpr ⟨(K.ncard : ℤ), s12⟩
  exact ⟨(H : Set G).ncard, Eq.symm (Set.Finite.cast_ncard_eq ((s2 : ((H : Set G) : Set G).Finite))), s13⟩

end Parley.Proofs.Wiedijk.Lagrange.Lagrange
