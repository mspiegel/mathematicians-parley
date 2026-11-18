module

public import Graphs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
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
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Graphs
public import Parley.Items.Stdlib.Sums

/-! Written from tests/notations/graphs.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Graphs.AWalkOfOneEdge

theorem a_walk_of_one_edge {α β : Type*} [Nonempty α] [Nonempty β] (V : Set α) (E : Set β) (G : β → Sym2 α) [LeanBridges.Graphs.Multigraph V E G] (e : ℤ → β) (hH2 : Set.MapsTo e (Set.Icc (1 : ℤ) (1 : ℤ) : Set ℤ) E) (v : ℤ → α) (hH3 : Set.MapsTo v (Set.Icc (0 : ℤ) (1 : ℤ) : Set ℤ) V) (hH4 : ∀ i : ℤ, i ∈ Finset.Icc 1 1 → G (e i) = Sym2.mk (v (i - 1)) (v i)) :
    G (e (1 : ℤ)) = Sym2.mk (v (0 : ℤ)) (v (1 : ℤ)) ∧ v (0 : ℤ) ∈ G (e (1 : ℤ)) ∧ ¬ v (0 : ℤ) = v (1 : ℤ) := by
  -- 1. def:range n := 1, k := 1
  have r68_1 : (1 : ℤ) ≤ 1 := by norm_num
  have s1 : (1 : ℤ) ∈ Finset.Icc (1 : ℤ) (1 : ℤ) := ((Parley.Items.Stdlib.Sums.def_range (k := (1 : ℤ)) (n := (1 : ℤ)))).mpr ⟨by norm_num, by norm_num⟩
  -- 2. mun:walk-step n := 1, i := 1, from H4, 1
  have s2 : G (e (1 : ℤ)) = Sym2.mk (v (1 - 1 : ℤ)) (v (1 : ℤ)) := by exact (Parley.Items.Stdlib.Graphs.mun_walk_step (V := V) (E := E) (G := G) (e := e) (v := v) (n := (1 : ℤ)) (by norm_num) (i := (1 : ℤ)) s1 hH4 hH2 hH3)
  -- 3. mun:walk-distinct n := 1, i := 1, from H4, 1
  have s3 : ¬ v (1 - 1 : ℤ) = v (1 : ℤ) := by exact (Parley.Items.Stdlib.Graphs.mun_walk_distinct (V := V) (E := E) (G := G) (e := e) (v := v) (n := (1 : ℤ)) (by norm_num) (i := (1 : ℤ)) s1 hH4 hH2 hH3)
  -- 4. arithmetic
  have s4 : (1 - 1 : ℤ) = 0 := by norm_num
  -- 5. substitute 1 − 1 = 0 (line 4) into line 2
  have s5 : G (e (1 : ℤ)) = Sym2.mk (v (0 : ℤ)) (v (1 : ℤ)) := by (have h := Eq.subst (motive := (fun t : ℤ => G (e (1 : ℤ)) = Sym2.mk (v t) (v (1 : ℤ)))) s4 s2; push_cast at h ⊢; exact_mod_cast h)
  -- 6. substitute 1 − 1 = 0 (line 4) into line 3
  have s6 : ¬ v (0 : ℤ) = v (1 : ℤ) := by (have h := Eq.subst (motive := (fun t : ℤ => ¬ v t = v (1 : ℤ))) s4 s3; push_cast at h ⊢; exact_mod_cast h)
  -- 7. mun:function-value f := e, x := 1, from 1
  have s7 : e (1 : ℤ) ∈ E := by exact (Parley.Items.Stdlib.Functions.mun_function_value (D := (Set.Icc (1 : ℤ) (1 : ℤ) : Set ℤ)) (E := E) (f := e) (x := (1 : ℤ)) (by simpa only [Finset.mem_Icc, Set.mem_Icc] using s1) hH2)
  -- 8. def:range0 n := 1, k := 0
  have r90_1 : (0 : ℤ) ≤ 1 := by norm_num
  have s8 : (0 : ℤ) ∈ Finset.Icc (0 : ℤ) (1 : ℤ) := ((Parley.Items.Stdlib.Sums.def_range0 (k := (0 : ℤ)) (n := (1 : ℤ)) (by norm_num))).mpr ⟨by norm_num, by norm_num⟩
  -- 9. def:range0 n := 1, k := 1
  have r94_1 : (1 : ℤ) ≤ 1 := by norm_num
  have s9 : (1 : ℤ) ∈ Finset.Icc (0 : ℤ) (1 : ℤ) := ((Parley.Items.Stdlib.Sums.def_range0 (k := (1 : ℤ)) (n := (1 : ℤ)) (by norm_num))).mpr ⟨by norm_num, by norm_num⟩
  -- 10. mun:function-value f := v, x := 0, from 8
  have s10 : v (0 : ℤ) ∈ V := by exact (Parley.Items.Stdlib.Functions.mun_function_value (D := (Set.Icc (0 : ℤ) (1 : ℤ) : Set ℤ)) (E := V) (f := v) (x := (0 : ℤ)) (by simpa only [Finset.mem_Icc, Set.mem_Icc] using s8) hH3)
  -- 11. mun:function-value f := v, x := 1, from 9
  have s11 : v (1 : ℤ) ∈ V := by exact (Parley.Items.Stdlib.Functions.mun_function_value (D := (Set.Icc (0 : ℤ) (1 : ℤ) : Set ℤ)) (E := V) (f := v) (x := (1 : ℤ)) (by simpa only [Finset.mem_Icc, Set.mem_Icc] using s9) hH3)
  -- 12. mun:joined-incident a := e(1), u := v(0), w := v(1), from 5, 7, 10, 11
  have s12a : v (0 : ℤ) ∈ G (e (1 : ℤ)) := by exact (Parley.Items.Stdlib.Graphs.mun_joined_incident_1 (E := E) (V := V) (a := e (1 : ℤ)) (u := v (0 : ℤ)) (w := v (1 : ℤ)) (G := G) s7 s10 s11 s5)
  have s12b : v (1 : ℤ) ∈ G (e (1 : ℤ)) := by exact (Parley.Items.Stdlib.Graphs.mun_joined_incident_2 (E := E) (V := V) (a := e (1 : ℤ)) (u := v (0 : ℤ)) (w := v (1 : ℤ)) (G := G) s7 s10 s11 s5)
  -- 13. join 5, 12, 6
  have s13a : G (e (1 : ℤ)) = Sym2.mk (v (0 : ℤ)) (v (1 : ℤ)) := s5
  have s13b : v (0 : ℤ) ∈ G (e (1 : ℤ)) := s12a
  have s13c : ¬ v (0 : ℤ) = v (1 : ℤ) := s6
  exact ⟨s13a, s13b, s13c⟩

end Parley.Tests.Notations.Graphs.AWalkOfOneEdge
