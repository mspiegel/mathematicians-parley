module

public import Graphs
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.Group.Even
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Graphs
public import Parley.Proofs.Wiedijk.Konigsberg.DegreeByWalk

/-! Written from proofs/wiedijk/konigsberg.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Konigsberg.WalkParity

theorem walk_parity {α β : Type*} [Nonempty α] [Nonempty β] (V : Set α) (E : Set β) (G : β → Sym2 α) [LeanBridges.Graphs.Multigraph V E G] (n : ℤ) (hH2 : 0 ≤ n) (e : ℤ → β) (hH3 : Set.MapsTo e (Set.Icc (1 : ℤ) n : Set ℤ) E) (v : ℤ → α) (hH4 : Set.MapsTo v (Set.Icc (0 : ℤ) n : Set ℤ) V) (hH5 : ((∀ i : ℤ, i ∈ Finset.Icc 1 n → G (e i) = Sym2.mk (v (i - 1)) (v i)) ∧ Set.MapsTo e (Set.Icc (1 : ℤ) n : Set ℤ) E ∧ Set.InjOn e (Set.Icc (1 : ℤ) n : Set ℤ)) ∧ (∀ a ∈ E, ∃ i : ℤ, i ∈ Finset.Icc 1 n ∧ a = e i)) (x : α) (hH6 : x ∈ V) (hH7 : ¬ x = v (0 : ℤ)) (hH8 : ¬ x = v n) :
    Even ({a ∈ E | x ∈ G a}.ncard : ℤ) := by
  -- 1. def:euler-path, from H5
  have s1a : ∀ i : ℤ, i ∈ Finset.Icc 1 n → G (e i) = Sym2.mk (v (i - 1)) (v i) := by exact (((Parley.Items.Stdlib.Graphs.def_euler_path (E := E) (V := V) (G := G) (e := e) (v := v) (n := n) hH2 hH3 hH4)).mp hH5).1.1
  have s1b : Set.MapsTo e (Set.Icc (1 : ℤ) n : Set ℤ) E ∧ Set.InjOn e (Set.Icc (1 : ℤ) n : Set ℤ) := by exact (((Parley.Items.Stdlib.Graphs.def_euler_path (E := E) (V := V) (G := G) (e := e) (v := v) (n := n) hH2 hH3 hH4)).mp hH5).1.2
  have s1c : ∀ a ∈ E, ∃ i : ℤ, i ∈ Finset.Icc 1 n ∧ a = e i := by exact (((Parley.Items.Stdlib.Graphs.def_euler_path (E := E) (V := V) (G := G) (e := e) (v := v) (n := n) hH2 hH3 hH4)).mp hH5).2
  -- 2. thm:degree-by-walk, from H6, 1
  have s2 : ({a ∈ E | x ∈ G a}.ncard : ℤ) = ({i ∈ (Set.Icc (1 : ℤ) n : Set ℤ) | x ∈ G (e i)}.ncard : ℤ) := by exact (Parley.Proofs.Wiedijk.Konigsberg.DegreeByWalk.degree_by_walk (V := V) (E := E) (G := G) (n := n) hH2 (e := e) s1b.1 s1b s1c (x := x) hH6)
  -- 3. proof
  have s3 : ∀ i : ℤ, i ∈ Finset.Icc 1 n → (x ∈ G (e i) ↔ x = v (i - 1) ∨ x = v i) := by
    intro i hK1
    have hK1_bounds := Finset.mem_Icc.mp hK1
    -- 3.1. mun:walk-step, from K1, 1
    have s3_1 : G (e i) = Sym2.mk (v (i - 1)) (v i) := by exact (Parley.Items.Stdlib.Graphs.mun_walk_step (V := V) (E := E) (G := G) (e := e) (v := v) (n := n) hH2 (i := i) hK1 s1a s1b.1 hH4)
    -- 3.2. mun:incident-of-joined a := e(i), u := v(i − 1), w := v(i), from H6, 3.1
    exact (Parley.Items.Stdlib.Graphs.mun_incident_of_joined (V := V) (x := x) (E := E) (G := G) (a := e i) (u := v (i - 1)) (w := v i) hH6 s3_1)
  -- 4. proof
  have s4 : ∀ i : ℤ, i ∈ Finset.Icc 1 n → ¬ (x = v (i - 1) ∧ x = v i) := by
    intro i hK2
    have hK2_bounds := Finset.mem_Icc.mp hK2
    intro hS1
    -- 4.1. mun:walk-distinct, from K2, 1
    have s4_1 : ¬ v (i - 1) = v i := by exact (Parley.Items.Stdlib.Graphs.mun_walk_distinct (V := V) (E := E) (G := G) (e := e) (v := v) (n := n) hH2 (i := i) hK2 s1a s1b.1 hH4)
    -- 4.2. calculation
    have s4_2 : v (i - 1) = v i := by
      calc v (i - 1) = x := hS1.1.symm
        _ = v i := hS1.2
    -- 4.3. restate 4.2
    have s4_3 : v (i - 1) = v i := by exact s4_2
    exact s4_1 s4_3
  set d : ℤ := ({i ∈ (Set.Icc (1 : ℤ) n : Set ℤ) | x = v (i - 1)}.ncard : ℤ) with hD1
  set r : ℤ := ({i ∈ (Set.Icc (1 : ℤ) n : Set ℤ) | x = v i}.ncard : ℤ) with hD2
  have hD3_kind : 0 ≤ ({i ∈ (Set.Icc (1 : ℤ) n : Set ℤ) | x = v (i - 1) ∨ x = v i}.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_count_nat0 (P := (fun i : ℤ => x = v (i - 1) ∨ x = v i)) (k := n))
  set c : ℤ := ({i ∈ (Set.Icc (1 : ℤ) n : Set ℤ) | x = v (i - 1) ∨ x = v i}.ncard : ℤ) with hD3
  have hD3_pos := hD3_kind
  -- 5. mun:count-either, from D1, D2, D3, 4
  have s5 : c = d + r := by
    simp only [hD1, hD2, hD3] at ⊢
    push_cast at ⊢
    (have h := (Parley.Items.Stdlib.Counting.mun_count_either (P := (fun i : ℤ => x = v (i - 1))) (Q := (fun i : ℤ => x = v i)) (n := n) s4); push_cast at h; exact h)
  have hD4_kind : 0 ≤ ({i ∈ (Set.Icc (1 : ℤ) (n - 1) : Set ℤ) | x = v i}.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_count_nat0 (P := (fun i : ℤ => x = v i)) (k := n - 1))
  set m : ℤ := ({i ∈ (Set.Icc (1 : ℤ) (n - 1) : Set ℤ) | x = v i}.ncard : ℤ) with hD4
  have hD4_pos := hD4_kind
  -- 6. calculation
  have s6 : d = m := by
    calc d = ({i ∈ (Set.Icc (0 : ℤ) (n - 1) : Set ℤ) | x = v i}.ncard : ℤ) := by
          simp only [hD1] at ⊢
          push_cast at ⊢
          (have h := (Parley.Items.Stdlib.Counting.mun_count_shift (P := (fun i : ℤ => x = v i)) (n := n)); push_cast at h; exact h)
      _ = ({i ∈ (Set.Icc (1 : ℤ) (n - 1) : Set ℤ) | x = v i}.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_count_first_fails (P := (fun i : ℤ => x = v i)) (m := n - 1) hH7)
      _ = m := by simp (disch := omega) only [hD4]
  -- 7. calculation
  have s7 : r = m := by
    calc r = ({i ∈ (Set.Icc (1 : ℤ) (n - 1) : Set ℤ) | x = v i}.ncard : ℤ) := by
          simp only [hD2] at ⊢
          push_cast at ⊢
          (have h := (Parley.Items.Stdlib.Counting.mun_count_last_fails (P := (fun i : ℤ => x = v i)) (n := n) hH8); push_cast at h; exact h)
      _ = m := by simp (disch := omega) only [hD4]
  -- 8. substitute
  have s8 : c = m + m := by
    have c1 : d = m := congrArg (fun t : ℤ => t) s6
    have row1 : c = m + r := Eq.subst (motive := (fun t : ℤ => c = t + r)) c1 s5
    have c2 : r = m := congrArg (fun t : ℤ => t) s7
    have row2 : c = m + m := Eq.subst (motive := (fun t : ℤ => c = m + t)) c2 row1
    exact row2
  -- 9. calculation
  have s9 : ({a ∈ E | x ∈ G a}.ncard : ℤ) = 2 * m := by
    calc ({a ∈ E | x ∈ G a}.ncard : ℤ) = ({i ∈ (Set.Icc (1 : ℤ) n : Set ℤ) | x ∈ G (e i)}.ncard : ℤ) := s2
      _ = c := by
          simp only [hD3] at ⊢
          push_cast at ⊢
          (have h := (Parley.Items.Stdlib.Counting.mun_count_same (P := (fun i : ℤ => x ∈ G (e i))) (Q := (fun i : ℤ => x = v (i - 1) ∨ x = v i)) (n := n) s3); push_cast at h; exact h)
      _ = m + m := s8
      _ = 2 * m := by ring1
  -- 10. def:even n := deg(x), from 9
  have r250_1 : 0 ≤ ({i ∈ (Set.Icc (1 : ℤ) n : Set ℤ) | x ∈ G (e i)}.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_count_nat0 (P := (fun i : ℤ => x ∈ G (e i))) (k := n))
  have r250_2 : 0 ≤ ({a ∈ E | x ∈ G a}.ncard : ℤ) := le_of_le_of_eq (r250_1) (s2).symm
  exact ((Parley.Items.Stdlib.Divisibility.def_even (n := ({a ∈ E | x ∈ G a}.ncard : ℤ)))).mpr ⟨m, s9⟩

end Parley.Proofs.Wiedijk.Konigsberg.WalkParity
