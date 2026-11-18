module

public import Counting
public import Graphs
public import Sets
public import Batteries.Tactic.Init
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Linter.Style
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Graphs
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Wiedijk.Konigsberg.DegreeByWalk
public import Parley.Proofs.Wiedijk.Konigsberg.WalkParity

/-! Written from proofs/wiedijk/konigsberg.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Konigsberg.OddVertices

theorem odd_vertices {α β : Type*} [Nonempty α] [Nonempty β] (V : Set α) (E : Set β) (G : β → Sym2 α) [LeanBridges.Graphs.Multigraph V E G] (hH2 : ∃ n : ℤ, 0 ≤ n ∧ (∃ e : ℤ → β, Set.MapsTo e (Set.Icc (1 : ℤ) n : Set ℤ) E ∧ (∃ v : ℤ → α, Set.MapsTo v (Set.Icc (0 : ℤ) n : Set ℤ) V ∧ (((∀ i : ℤ, i ∈ Finset.Icc 1 n → G (e i) = Sym2.mk (v (i - 1)) (v i)) ∧ Set.MapsTo e (Set.Icc (1 : ℤ) n : Set ℤ) E ∧ Set.InjOn e (Set.Icc (1 : ℤ) n : Set ℤ)) ∧ (∀ a ∈ E, ∃ i : ℤ, i ∈ Finset.Icc 1 n ∧ a = e i))))) :
    {x ∈ V | ∃ m : ℕ, {a ∈ E | x ∈ G a}.encard = (m : ℕ∞) ∧ Odd (m : ℤ)}.encard ≤ ((2 : ℕ) : ℕ∞) := by
  -- 1. obtain n, e, v: def:traversable, from H2
  obtain ⟨n, s1a, e, s1b, v, s1c, s1d⟩ := ((Parley.Items.Stdlib.Graphs.def_traversable (E := E) (V := V) (G := G))).mp hH2
  -- 2. def:euler-path, from 1
  have s2a : ∀ i : ℤ, i ∈ Finset.Icc 1 n → G (e i) = Sym2.mk (v (i - 1)) (v i) := by exact (((Parley.Items.Stdlib.Graphs.def_euler_path (E := E) (V := V) (G := G) (e := e) (v := v) (n := n) s1a s1b s1c)).mp s1d).1.1
  have s2b : Set.MapsTo e (Set.Icc (1 : ℤ) n : Set ℤ) E ∧ Set.InjOn e (Set.Icc (1 : ℤ) n : Set ℤ) := by exact (((Parley.Items.Stdlib.Graphs.def_euler_path (E := E) (V := V) (G := G) (e := e) (v := v) (n := n) s1a s1b s1c)).mp s1d).1.2
  have s2c : ∀ a ∈ E, ∃ i : ℤ, i ∈ Finset.Icc 1 n ∧ a = e i := by exact (((Parley.Items.Stdlib.Graphs.def_euler_path (E := E) (V := V) (G := G) (e := e) (v := v) (n := n) s1a s1b s1c)).mp s1d).2
  -- 3. proof
  have s3 : ∀ u ∈ {x ∈ V | Odd ({a ∈ E | x ∈ G a}.ncard : ℤ)}, u ∈ ({v (0 : ℤ), v n} : Set α) := by
    intro u hK1
    -- 3.1. def:set-builder, from K1
    have s3_1a : u ∈ V := by exact (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun x : α => Odd ({a ∈ E | x ∈ G a}.ncard : ℤ))) (X := V) (u := u))).mp hK1).1
    have s3_1b : Odd ({a ∈ E | u ∈ G a}.ncard : ℤ) := by
      have hI : Odd ({b ∈ E | u ∈ G b}.ncard : ℤ) := by exact ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun x : α => Odd ({a ∈ E | x ∈ G a}.ncard : ℤ))) (X := V) (u := u))).mp hK1).2)
      exact hI
    -- 3.2. axi:excluded-middle
    have s3_2 : u = v (0 : ℤ) ∨ ¬ u = v (0 : ℤ) := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := u = v (0 : ℤ)))
    -- 3.3. cases, from 3.2
    have s3_3 : u = v (0 : ℤ) ∨ u = v n := by
      rcases s3_2 with hC1 | hC2
      · skip
        -- 3.3.1. mun:or-left, from C1
        exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := u = v (0 : ℤ)) (Q := u = v n) hC1)
      · skip
        -- 3.3.2. contradiction
        have s3_3_2 : u = v n := by
          by_contra hS1
          -- 3.3.2.1. thm:walk-parity x := u, from C2, S1, 1, 3.1
          have s3_3_2_1 : Even ({a ∈ E | u ∈ G a}.ncard : ℤ) := by exact (Parley.Proofs.Wiedijk.Konigsberg.WalkParity.walk_parity (V := V) (E := E) (G := G) (n := n) s1a (e := e) s1b (v := v) s1c s1d (x := u) s3_1a hC2 hS1)
          -- 3.3.2.2. mun:not-both, from 3.3.2.1
          have r300_1 : ({a ∈ E | u ∈ G a}.ncard : ℤ) = ({i ∈ (Set.Icc (1 : ℤ) n : Set ℤ) | u ∈ G (e i)}.ncard : ℤ) := by exact (Parley.Proofs.Wiedijk.Konigsberg.DegreeByWalk.degree_by_walk (V := V) (E := E) (G := G) (n := n) s1a (e := e) s2b.1 s2b s2c (x := u) s3_1a)
          have r300_2 : 0 ≤ ({i ∈ (Set.Icc (1 : ℤ) n : Set ℤ) | u ∈ G (e i)}.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_count_nat0 (P := (fun i : ℤ => u ∈ G (e i))) (k := n))
          have s3_3_2_2 : ¬ Odd ({a ∈ E | u ∈ G a}.ncard : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := ({a ∈ E | u ∈ G a}.ncard : ℤ)) s3_3_2_1)
          exact s3_3_2_2 s3_1b
        -- 3.3.3. mun:or-right, from 3.3.2
        exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := u = v (0 : ℤ)) (Q := u = v n) s3_3_2)
    -- 3.4. def:pair x := u, from 3.3
    exact ((Parley.Items.Stdlib.Sets.def_pair (u := v (0 : ℤ)) (w := v n) (x := u))).mpr s3_3
  -- 4. def:subset, from 3
  have s4 : {x ∈ V | Odd ({a ∈ E | x ∈ G a}.ncard : ℤ)} ⊆ ({v (0 : ℤ), v n} : Set α) := ((Parley.Items.Stdlib.Sets.def_subset (X := {x ∈ V | Odd ({a ∈ E | x ∈ G a}.ncard : ℤ)}) (Y := ({v (0 : ℤ), v n} : Set α)))).mpr s3
  -- 5. mun:card-subset, from 4
  have s5 : ({x ∈ V | Odd ({a ∈ E | x ∈ G a}.ncard : ℤ)}.ncard : ℤ) ≤ (({v (0 : ℤ), v n} : Set α).ncard : ℤ) := by (have h := (Parley.Items.Stdlib.Counting.mun_card_subset (A := {x ∈ V | Odd ({a ∈ E | x ∈ G a}.ncard : ℤ)}) (B := ({v (0 : ℤ), v n} : Set α)) s4); simp only [← Set.Finite.cast_ncard_eq (((Set.toFinite _).subset s4 : ({x ∈ V | Odd ({a ∈ E | x ∈ G a}.ncard : ℤ)} : Set α).Finite)), ← Set.Finite.cast_ncard_eq ((Set.toFinite _ : (({v (0 : ℤ), v n} : Set α) : Set α).Finite))] at h ⊢; exact_mod_cast h)
  -- 6. mun:card-pair u := v(0), w := v(n)
  have s6 : (({v (0 : ℤ), v n} : Set α).ncard : ℤ) ≤ 2 := by exact (Parley.Items.Stdlib.Counting.mun_card_pair (u := v (0 : ℤ)) (w := v n))
  -- 7. transitivity, from 5, 6
  have r321_1 : ({v (0 : ℤ), v n} : Set α).Finite := by exact (Parley.Items.Stdlib.Sets.mun_pair_finite (u := v (0 : ℤ)) (w := v n))
  have r321_2 : {x ∈ V | Odd ({a ∈ E | x ∈ G a}.ncard : ℤ)}.Finite := by exact (Parley.Items.Stdlib.Counting.mun_finite_part (X := ({v (0 : ℤ), v n} : Set α)) (Y := {x ∈ V | Odd ({a ∈ E | x ∈ G a}.ncard : ℤ)}) r321_1 s4)
  have r321_3 : 0 ≤ ({x ∈ V | Odd ({a ∈ E | x ∈ G a}.ncard : ℤ)}.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := {x ∈ V | Odd ({a ∈ E | x ∈ G a}.ncard : ℤ)}) r321_2)
  have r321_4 : 0 ≤ (({v (0 : ℤ), v n} : Set α).ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := ({v (0 : ℤ), v n} : Set α)) r321_1)
  have s7 : ({x ∈ V | Odd ({a ∈ E | x ∈ G a}.ncard : ℤ)}.ncard : ℤ) ≤ 2 := by exact le_trans s5 s6
  show {x ∈ V | ∃ m : ℕ, {a ∈ E | x ∈ G a}.encard = (m : ℕ∞) ∧ Odd (m : ℤ)}.encard ≤ ((2 : ℕ) : ℕ∞); simp (disch := exact Set.Finite.subset (LeanBridges.Sets.finite_of_covered_by_range _ _ _ s2c) (Set.sep_subset _ _)) only [LeanBridges.Counting.some_count_iff]; ((have h := s7; simp only [← Set.Finite.cast_ncard_eq (((Set.toFinite _).subset s4 : ({x ∈ V | Odd ({a ∈ E | x ∈ G a}.ncard : ℤ)} : Set α).Finite))] at h ⊢; exact_mod_cast h))

end Parley.Proofs.Wiedijk.Konigsberg.OddVertices
