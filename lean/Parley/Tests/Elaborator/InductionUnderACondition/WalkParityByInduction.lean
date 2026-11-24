module

public import Functions
public import Graphs
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
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
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Graphs
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sets
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/induction-under-a-condition.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.InductionUnderACondition.WalkParityByInduction

theorem walk_parity_by_induction {α β : Type*} [Nonempty α] [Nonempty β] (V : Set α) (E : Set β) (G : β → Sym2 α) [LeanBridges.Graphs.Multigraph V E G] (n : ℤ) (hH2 : 0 ≤ n) (e : ℤ → β) (hH3 : Set.MapsTo e (Set.Icc (1 : ℤ) n : Set ℤ) E) (v : ℤ → α) (hH4 : Set.MapsTo v (Set.Icc (0 : ℤ) n : Set ℤ) V) (hH5 : ∀ i : ℤ, i ∈ Finset.Icc 1 n → G (e i) = Sym2.mk (v (i - 1)) (v i)) (k : ℤ) (hH6 : k ∈ Finset.Icc (0 : ℤ) n) (x : α) (hH7 : x ∈ V \ ({v (0 : ℤ)} : Set α)) :
    (Odd ({i ∈ (Set.Icc (1 : ℤ) k : Set ℤ) | x ∈ G (e i)}.ncard : ℤ) ↔ x = v k) := by
  -- 1. induction on j starting at 0
  have s1 : ∀ j : ℤ, 0 ≤ j → j ≤ n → (∀ y ∈ V \ ({v (0 : ℤ)} : Set α), Odd ({i ∈ (Set.Icc (1 : ℤ) j : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) ↔ y = v j) := by
    intro j h_j
    replace h_j : 0 ≤ j := by omega
    induction j, h_j using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. proof
      intro hC1
      intro y hK1
      -- 1.1.1. def:difference, from K1
      have s1_1_1a : y ∈ V := by exact (((Parley.Items.Stdlib.Sets.def_difference (Y := V) (Z := ({v (0 : ℤ)} : Set α)) (u := y))).mp hK1).1
      have s1_1_1b : ¬ y ∈ ({v (0 : ℤ)} : Set α) := by exact (((Parley.Items.Stdlib.Sets.def_difference (Y := V) (Z := ({v (0 : ℤ)} : Set α)) (u := y))).mp hK1).2
      -- 1.1.2. D1
      have r57_1 : y ∈ V := by exact s1_1_1a
      have s1_1_2 : ({i ∈ (Set.Icc (1 : ℤ) (0 : ℤ) : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) = ({i ∈ (Set.Icc (1 : ℤ) (0 : ℤ) : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) := rfl
      -- 1.1.3. mun:count-empty-range
      have s1_1_3 : ({i ∈ (Set.Icc (1 : ℤ) (0 : ℤ) : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) = 0 := by exact (Parley.Items.Stdlib.Counting.mun_count_empty_range (P := (fun i : ℤ => y ∈ G (e i))))
      -- 1.1.4. arithmetic
      have s1_1_4 : (0 : ℤ) = 2 * 0 := by norm_num
      -- 1.1.5. calculation
      have s1_1_5 : ({i ∈ (Set.Icc (1 : ℤ) (0 : ℤ) : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) = 2 * 0 := by
        calc ({i ∈ (Set.Icc (1 : ℤ) (0 : ℤ) : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) = ({i ∈ (Set.Icc (1 : ℤ) (0 : ℤ) : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) := rfl
          _ = 0 := s1_1_3
          _ = 2 * 0 := s1_1_4
      -- 1.1.6. def:even n := c(0, y), from 1.1.5
      have s1_1_6 : Even ({i ∈ (Set.Icc (1 : ℤ) (0 : ℤ) : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) := ((Parley.Items.Stdlib.Divisibility.def_even (n := ({i ∈ (Set.Icc (1 : ℤ) (0 : ℤ) : Set ℤ) | y ∈ G (e i)}.ncard : ℤ)))).mpr ⟨(0 : ℤ), s1_1_5⟩
      -- 1.1.7. mun:not-both n := c(0, y), from 1.1.6
      have r76_1 : 0 ≤ ({i ∈ (Set.Icc (1 : ℤ) (0 : ℤ) : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_count_nat0 (P := (fun i : ℤ => y ∈ G (e i))) (k := (0 : ℤ)))
      have s1_1_7 : ¬ Odd ({i ∈ (Set.Icc (1 : ℤ) (0 : ℤ) : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := ({i ∈ (Set.Icc (1 : ℤ) (0 : ℤ) : Set ℤ) | y ∈ G (e i)}.ncard : ℤ)) s1_1_6)
      -- 1.1.8. contradiction
      have s1_1_8 : ¬ y = v (0 : ℤ) := by
        intro hS1
        -- 1.1.8.1. def:singleton, from S1
        have s1_1_8_1 : y ∈ ({v (0 : ℤ)} : Set α) := ((Parley.Items.Stdlib.Sets.def_singleton (a := v (0 : ℤ)) (x := y))).mpr hS1
        exact s1_1_1b s1_1_8_1
      -- 1.1.9. mun:iff-both-false, from 1.1.7, 1.1.8
      exact (Parley.Items.Stdlib.Reasoning.mun_iff_both_false (P := Odd ({i ∈ (Set.Icc (1 : ℤ) (0 : ℤ) : Set ℤ) | y ∈ G (e i)}.ncard : ℤ)) (Q := y = v (0 : ℤ)) s1_1_7 s1_1_8)
    | succ j hK2 hIH =>
      -- 1.2. proof
      intro hC2
      intro y hK3
      -- 1.2.1. def:difference, from K3
      have s1_2_1a : y ∈ V := by exact (((Parley.Items.Stdlib.Sets.def_difference (Y := V) (Z := ({v (0 : ℤ)} : Set α)) (u := y))).mp hK3).1
      have s1_2_1b : ¬ y ∈ ({v (0 : ℤ)} : Set α) := by exact (((Parley.Items.Stdlib.Sets.def_difference (Y := V) (Z := ({v (0 : ℤ)} : Set α)) (u := y))).mp hK3).2
      -- 1.2.2. def:range k := j + 1, from C2
      have r103_1 : 0 < j + 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat0_successor (k := j) hK2)
      have s1_2_2 : j + 1 ∈ Finset.Icc (1 : ℤ) n := ((Parley.Items.Stdlib.Sums.def_range (k := j + 1) (n := n))).mpr ⟨r103_1, hC2⟩
      -- 1.2.3. inequalities, from C2
      have s1_2_3 : j ≤ n := by linarith only [hC2]
      -- 1.2.4. def:range0 k := j, from 1.2.3
      have s1_2_4 : j ∈ Finset.Icc (0 : ℤ) n := ((Parley.Items.Stdlib.Sums.def_range0 (k := j) (n := n) hH2)).mpr ⟨hK2, s1_2_3⟩
      -- 1.2.5. def:range0 k := j + 1, from C2
      have s1_2_5 : j + 1 ∈ Finset.Icc (0 : ℤ) n := ((Parley.Items.Stdlib.Sums.def_range0 (k := j + 1) (n := n) hH2)).mpr ⟨add_nonneg (hK2) (by norm_num), hC2⟩
      -- 1.2.6. mun:walk-step i := j + 1, from H5, 1.2.2
      have s1_2_6 : G (e (j + 1)) = Sym2.mk (v (j + 1 - 1)) (v (j + 1)) := by exact (Parley.Items.Stdlib.Graphs.mun_walk_step (V := V) (E := E) (G := G) (e := e) (v := v) (n := n) hH2 (i := j + 1) s1_2_2 hH5 hH3 hH4)
      -- 1.2.7. algebra
      have s1_2_7 : j + 1 - 1 = j := by ring1
      -- 1.2.8. substitute j + 1 − 1 = j (line 1.2.7) into line 1.2.6
      have s1_2_8 : G (e (j + 1)) = Sym2.mk (v j) (v (j + 1)) := Eq.subst (motive := (fun t : ℤ => G (e (j + 1)) = Sym2.mk (v t) (v (j + 1)))) s1_2_7 s1_2_6
      -- 1.2.9. mun:modus-ponens, from IH, 1.2.3
      have s1_2_9 : ∀ y ∈ V \ ({v (0 : ℤ)} : Set α), Odd ({i ∈ (Set.Icc (1 : ℤ) j : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) ↔ y = v j := by exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := j ≤ n) (Q := ∀ y ∈ V \ ({v (0 : ℤ)} : Set α), Odd ({i ∈ (Set.Icc (1 : ℤ) j : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) ↔ y = v j) hIH s1_2_3)
      -- 1.2.10. instantiate y := y in line 1.2.9, from K3
      have s1_2_10 : Odd ({i ∈ (Set.Icc (1 : ℤ) j : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) ↔ y = v j := by exact (s1_2_9 y hK3)
      -- 1.2.11. axi:excluded-middle
      have s1_2_11 : y = v (j + 1) ∨ ¬ y = v (j + 1) := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := y = v (j + 1)))
      -- 1.2.12. cases, from 1.2.11
      rcases s1_2_11 with hC3 | hC4
      · skip
        -- 1.2.12.1. mun:join-distinct a := e(j + 1), u := v(j), w := v(j + 1), from 1.2.8
        have r140_1 : e (j + 1) ∈ E := by exact (Parley.Items.Stdlib.Functions.mun_function_value (D := (Set.Icc (1 : ℤ) n : Set ℤ)) (E := E) (f := e) (x := j + 1) (by simpa only [Finset.mem_Icc, Set.mem_Icc] using s1_2_2) hH3)
        have r140_2 : v j ∈ V := by exact (Parley.Items.Stdlib.Functions.mun_function_value (D := (Set.Icc (0 : ℤ) n : Set ℤ)) (E := V) (f := v) (x := j) (by simpa only [Finset.mem_Icc, Set.mem_Icc] using s1_2_4) hH4)
        have r140_3 : v (j + 1) ∈ V := by exact (Parley.Items.Stdlib.Functions.mun_function_value (D := (Set.Icc (0 : ℤ) n : Set ℤ)) (E := V) (f := v) (x := j + 1) (by simpa only [Finset.mem_Icc, Set.mem_Icc] using s1_2_5) hH4)
        have s1_2_12_1 : ¬ v j = v (j + 1) := by exact (Parley.Items.Stdlib.Graphs.mun_join_distinct (E := E) (V := V) (a := e (j + 1)) (u := v j) (w := v (j + 1)) (G := G) r140_1 r140_2 r140_3 s1_2_8)
        -- 1.2.12.2. substitute y = v(j + 1) (C3) into line 1.2.12.1
        have s1_2_12_2 : ¬ y = v j := by apply Ne.symm; exact Eq.subst (motive := (fun t : α => ¬ v j = t)) hC3.symm s1_2_12_1
        -- 1.2.12.3. mun:iff-not-from-right, from 1.2.10, 1.2.12.2
        have s1_2_12_3 : ¬ Odd ({i ∈ (Set.Icc (1 : ℤ) j : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) := by exact (Parley.Items.Stdlib.Reasoning.mun_iff_not_from_right (P := Odd ({i ∈ (Set.Icc (1 : ℤ) j : Set ℤ) | y ∈ G (e i)}.ncard : ℤ)) (Q := y = v j) s1_2_10 s1_2_12_2)
        -- 1.2.12.4. mun:even-or-odd n := c(j, y)
        have r153_1 : 0 ≤ ({i ∈ (Set.Icc (1 : ℤ) j : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_count_nat0 (P := (fun i : ℤ => y ∈ G (e i))) (k := j))
        have s1_2_12_4 : Even ({i ∈ (Set.Icc (1 : ℤ) j : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) ∨ Odd ({i ∈ (Set.Icc (1 : ℤ) j : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := ({i ∈ (Set.Icc (1 : ℤ) j : Set ℤ) | y ∈ G (e i)}.ncard : ℤ)))
        -- 1.2.12.5. mun:disjunctive-syllogism, from 1.2.12.3, 1.2.12.4
        have s1_2_12_5 : Even ({i ∈ (Set.Icc (1 : ℤ) j : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) := by exact (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even ({i ∈ (Set.Icc (1 : ℤ) j : Set ℤ) | y ∈ G (e i)}.ncard : ℤ)) (Q := Odd ({i ∈ (Set.Icc (1 : ℤ) j : Set ℤ) | y ∈ G (e i)}.ncard : ℤ)) s1_2_12_4 s1_2_12_3)
        -- 1.2.12.6. mun:joined-incident a := e(j + 1), u := v(j), w := v(j + 1), from 1.2.8
        have r160_1 : e (j + 1) ∈ E := by exact (Parley.Items.Stdlib.Functions.mun_function_value (D := (Set.Icc (1 : ℤ) n : Set ℤ)) (E := E) (f := e) (x := j + 1) (by simpa only [Finset.mem_Icc, Set.mem_Icc] using s1_2_2) hH3)
        have r160_2 : v j ∈ V := by exact (Parley.Items.Stdlib.Functions.mun_function_value (D := (Set.Icc (0 : ℤ) n : Set ℤ)) (E := V) (f := v) (x := j) (by simpa only [Finset.mem_Icc, Set.mem_Icc] using s1_2_4) hH4)
        have r160_3 : v (j + 1) ∈ V := by exact (Parley.Items.Stdlib.Functions.mun_function_value (D := (Set.Icc (0 : ℤ) n : Set ℤ)) (E := V) (f := v) (x := j + 1) (by simpa only [Finset.mem_Icc, Set.mem_Icc] using s1_2_5) hH4)
        have s1_2_12_6 : v (j + 1) ∈ G (e (j + 1)) := by exact (Parley.Items.Stdlib.Graphs.mun_joined_incident_2 (E := E) (V := V) (a := e (j + 1)) (u := v j) (w := v (j + 1)) (G := G) r160_1 r160_2 r160_3 s1_2_8)
        -- 1.2.12.7. substitute y = v(j + 1) (C3) into line 1.2.12.6
        have s1_2_12_7 : y ∈ G (e (j + 1)) := Eq.subst (motive := (fun t : α => t ∈ G (e (j + 1)))) hC3.symm s1_2_12_6
        -- 1.2.12.8. mun:count-step-holds k := j, from D1, 1.2.12.7
        have r170_1 : y ∈ V := by exact s1_2_1a
        have s1_2_12_8 : ({i ∈ (Set.Icc (1 : ℤ) (j + 1) : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) = ({i ∈ (Set.Icc (1 : ℤ) j : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) + 1 := by exact (Parley.Items.Stdlib.Counting.mun_count_step_holds (P := (fun i : ℤ => y ∈ G (e i))) (k := j) hK2 s1_2_12_7)
        -- 1.2.12.9. obtain m: def:even n := c(j, y), from 1.2.12.5
        have r174_1 : 0 ≤ ({i ∈ (Set.Icc (1 : ℤ) j : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_count_nat0 (P := (fun i : ℤ => y ∈ G (e i))) (k := j))
        obtain ⟨m, s1_2_12_9⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := ({i ∈ (Set.Icc (1 : ℤ) j : Set ℤ) | y ∈ G (e i)}.ncard : ℤ)))).mp s1_2_12_5
        -- 1.2.12.10. substitute c(j, y) = 2m (line 1.2.12.9) into line 1.2.12.8
        have s1_2_12_10 : ({i ∈ (Set.Icc (1 : ℤ) (j + 1) : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) = 2 * m + 1 := Eq.subst (motive := (fun t : ℤ => ({i ∈ (Set.Icc (1 : ℤ) (j + 1) : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) = t + 1)) s1_2_12_9 s1_2_12_8
        -- 1.2.12.11. def:odd n := c(j + 1, y), from 1.2.12.10
        have s1_2_12_11 : Odd ({i ∈ (Set.Icc (1 : ℤ) (j + 1) : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) := ((Parley.Items.Stdlib.Divisibility.def_odd (n := ({i ∈ (Set.Icc (1 : ℤ) (j + 1) : Set ℤ) | y ∈ G (e i)}.ncard : ℤ)))).mpr ⟨m, s1_2_12_10⟩
        -- 1.2.12.12. mun:iff-both-true, from C3, 1.2.12.11
        exact (Parley.Items.Stdlib.Reasoning.mun_iff_both_true (P := Odd ({i ∈ (Set.Icc (1 : ℤ) (j + 1) : Set ℤ) | y ∈ G (e i)}.ncard : ℤ)) (Q := y = v (j + 1)) s1_2_12_11 hC3)
      · skip
        -- 1.2.12.13. axi:excluded-middle
        have s1_2_12_13 : y = v j ∨ ¬ y = v j := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := y = v j))
        -- 1.2.12.14. cases, from 1.2.12.13
        have s1_2_12_14 : Even ({i ∈ (Set.Icc (1 : ℤ) (j + 1) : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) := by
          rcases s1_2_12_13 with hC5 | hC6
          · skip
            -- 1.2.12.14.1. mun:joined-incident a := e(j + 1), u := v(j), w := v(j + 1), from 1.2.8
            have r199_1 : e (j + 1) ∈ E := by exact (Parley.Items.Stdlib.Functions.mun_function_value (D := (Set.Icc (1 : ℤ) n : Set ℤ)) (E := E) (f := e) (x := j + 1) (by simpa only [Finset.mem_Icc, Set.mem_Icc] using s1_2_2) hH3)
            have r199_2 : v j ∈ V := by exact (Parley.Items.Stdlib.Functions.mun_function_value (D := (Set.Icc (0 : ℤ) n : Set ℤ)) (E := V) (f := v) (x := j) (by simpa only [Finset.mem_Icc, Set.mem_Icc] using s1_2_4) hH4)
            have r199_3 : v (j + 1) ∈ V := by exact (Parley.Items.Stdlib.Functions.mun_function_value (D := (Set.Icc (0 : ℤ) n : Set ℤ)) (E := V) (f := v) (x := j + 1) (by simpa only [Finset.mem_Icc, Set.mem_Icc] using s1_2_5) hH4)
            have s1_2_12_14_1 : v j ∈ G (e (j + 1)) := by exact (Parley.Items.Stdlib.Graphs.mun_joined_incident_1 (E := E) (V := V) (a := e (j + 1)) (u := v j) (w := v (j + 1)) (G := G) r199_1 r199_2 r199_3 s1_2_8)
            -- 1.2.12.14.2. substitute y = v(j) (C5) into line 1.2.12.14.1
            have s1_2_12_14_2 : y ∈ G (e (j + 1)) := Eq.subst (motive := (fun t : α => t ∈ G (e (j + 1)))) hC5.symm s1_2_12_14_1
            -- 1.2.12.14.3. mun:count-step-holds k := j, from D1, 1.2.12.14.2
            have r209_1 : y ∈ V := by exact s1_2_1a
            have s1_2_12_14_3 : ({i ∈ (Set.Icc (1 : ℤ) (j + 1) : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) = ({i ∈ (Set.Icc (1 : ℤ) j : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) + 1 := by exact (Parley.Items.Stdlib.Counting.mun_count_step_holds (P := (fun i : ℤ => y ∈ G (e i))) (k := j) hK2 s1_2_12_14_2)
            -- 1.2.12.14.4. mun:iff-from-right, from C5, 1.2.10
            have s1_2_12_14_4 : Odd ({i ∈ (Set.Icc (1 : ℤ) j : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) := by exact (Parley.Items.Stdlib.Reasoning.mun_iff_from_right (P := Odd ({i ∈ (Set.Icc (1 : ℤ) j : Set ℤ) | y ∈ G (e i)}.ncard : ℤ)) (Q := y = v j) s1_2_10 hC5)
            -- 1.2.12.14.5. obtain m: def:odd n := c(j, y), from 1.2.12.14.4
            have r216_1 : 0 ≤ ({i ∈ (Set.Icc (1 : ℤ) j : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_count_nat0 (P := (fun i : ℤ => y ∈ G (e i))) (k := j))
            obtain ⟨m, s1_2_12_14_5⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := ({i ∈ (Set.Icc (1 : ℤ) j : Set ℤ) | y ∈ G (e i)}.ncard : ℤ)))).mp s1_2_12_14_4
            -- 1.2.12.14.6. substitute c(j, y) = 2m + 1 (line 1.2.12.14.5) into line 1.2.12.14.3
            have s1_2_12_14_6 : ({i ∈ (Set.Icc (1 : ℤ) (j + 1) : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) = 2 * m + 1 + 1 := Eq.subst (motive := (fun t : ℤ => ({i ∈ (Set.Icc (1 : ℤ) (j + 1) : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) = t + 1)) s1_2_12_14_5 s1_2_12_14_3
            -- 1.2.12.14.7. algebra
            have s1_2_12_14_7 : 2 * m + 1 + 1 = 2 * (m + 1) := by ring1
            -- 1.2.12.14.8. calculation
            have s1_2_12_14_8 : ({i ∈ (Set.Icc (1 : ℤ) (j + 1) : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) = 2 * (m + 1) := by
              calc ({i ∈ (Set.Icc (1 : ℤ) (j + 1) : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) = 2 * m + 1 + 1 := s1_2_12_14_6
                _ = 2 * (m + 1) := s1_2_12_14_7
            -- 1.2.12.14.9. def:even n := c(j + 1, y), from 1.2.12.14.8
            exact ((Parley.Items.Stdlib.Divisibility.def_even (n := ({i ∈ (Set.Icc (1 : ℤ) (j + 1) : Set ℤ) | y ∈ G (e i)}.ncard : ℤ)))).mpr ⟨m + 1, s1_2_12_14_8⟩
          · skip
            -- 1.2.12.14.10. mun:not-incident a := e(j + 1), u := v(j), w := v(j + 1), from C4, C6, 1.2.8
            have r237_1 : e (j + 1) ∈ E := by exact (Parley.Items.Stdlib.Functions.mun_function_value (D := (Set.Icc (1 : ℤ) n : Set ℤ)) (E := E) (f := e) (x := j + 1) (by simpa only [Finset.mem_Icc, Set.mem_Icc] using s1_2_2) hH3)
            have r237_2 : v j ∈ V := by exact (Parley.Items.Stdlib.Functions.mun_function_value (D := (Set.Icc (0 : ℤ) n : Set ℤ)) (E := V) (f := v) (x := j) (by simpa only [Finset.mem_Icc, Set.mem_Icc] using s1_2_4) hH4)
            have r237_3 : v (j + 1) ∈ V := by exact (Parley.Items.Stdlib.Functions.mun_function_value (D := (Set.Icc (0 : ℤ) n : Set ℤ)) (E := V) (f := v) (x := j + 1) (by simpa only [Finset.mem_Icc, Set.mem_Icc] using s1_2_5) hH4)
            have r237_4 : y ∈ V := by exact s1_2_1a
            have s1_2_12_14_10 : ¬ y ∈ G (e (j + 1)) := by exact (Parley.Items.Stdlib.Graphs.mun_not_incident (E := E) (V := V) (a := e (j + 1)) (u := v j) (w := v (j + 1)) (x := y) (G := G) r237_1 r237_2 r237_3 r237_4 s1_2_8 hC6 hC4)
            -- 1.2.12.14.11. mun:count-step-fails k := j, from D1, 1.2.12.14.10
            have r245_1 : y ∈ V := by exact s1_2_1a
            have s1_2_12_14_11 : ({i ∈ (Set.Icc (1 : ℤ) (j + 1) : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) = ({i ∈ (Set.Icc (1 : ℤ) j : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_count_step_fails (P := (fun i : ℤ => y ∈ G (e i))) (k := j) hK2 s1_2_12_14_10)
            -- 1.2.12.14.12. mun:iff-not-from-right, from C6, 1.2.10
            have s1_2_12_14_12 : ¬ Odd ({i ∈ (Set.Icc (1 : ℤ) j : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) := by exact (Parley.Items.Stdlib.Reasoning.mun_iff_not_from_right (P := Odd ({i ∈ (Set.Icc (1 : ℤ) j : Set ℤ) | y ∈ G (e i)}.ncard : ℤ)) (Q := y = v j) s1_2_10 hC6)
            -- 1.2.12.14.13. mun:even-or-odd n := c(j, y)
            have r252_1 : 0 ≤ ({i ∈ (Set.Icc (1 : ℤ) j : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_count_nat0 (P := (fun i : ℤ => y ∈ G (e i))) (k := j))
            have s1_2_12_14_13 : Even ({i ∈ (Set.Icc (1 : ℤ) j : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) ∨ Odd ({i ∈ (Set.Icc (1 : ℤ) j : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := ({i ∈ (Set.Icc (1 : ℤ) j : Set ℤ) | y ∈ G (e i)}.ncard : ℤ)))
            -- 1.2.12.14.14. mun:disjunctive-syllogism, from 1.2.12.14.12, 1.2.12.14.13
            have s1_2_12_14_14 : Even ({i ∈ (Set.Icc (1 : ℤ) j : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) := by exact (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even ({i ∈ (Set.Icc (1 : ℤ) j : Set ℤ) | y ∈ G (e i)}.ncard : ℤ)) (Q := Odd ({i ∈ (Set.Icc (1 : ℤ) j : Set ℤ) | y ∈ G (e i)}.ncard : ℤ)) s1_2_12_14_13 s1_2_12_14_12)
            -- 1.2.12.14.15. substitute c(j + 1, y) = c(j, y) (line 1.2.12.14.11) into line 1.2.12.14.14
            have r259_1 : 0 ≤ ({i ∈ (Set.Icc (1 : ℤ) j : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_count_nat0 (P := (fun i : ℤ => y ∈ G (e i))) (k := j))
            have e_nat : {i ∈ (Set.Icc (1 : ℤ) j : Set ℤ) | y ∈ G (e i)}.ncard = {i ∈ (Set.Icc (1 : ℤ) (j + 1) : Set ℤ) | y ∈ G (e i)}.ncard := by exact_mod_cast s1_2_12_14_11.symm
            exact Eq.subst (motive := (fun t : ℕ => Even (t : ℤ))) e_nat s1_2_12_14_14
        -- 1.2.12.15. mun:not-both n := c(j + 1, y), from 1.2.12.14
        have r263_1 : 0 ≤ ({i ∈ (Set.Icc (1 : ℤ) (j + 1) : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_count_nat0 (P := (fun i : ℤ => y ∈ G (e i))) (k := j + 1))
        have s1_2_12_15 : ¬ Odd ({i ∈ (Set.Icc (1 : ℤ) (j + 1) : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := ({i ∈ (Set.Icc (1 : ℤ) (j + 1) : Set ℤ) | y ∈ G (e i)}.ncard : ℤ)) s1_2_12_14)
        -- 1.2.12.16. mun:iff-both-false, from C4, 1.2.12.15
        exact (Parley.Items.Stdlib.Reasoning.mun_iff_both_false (P := Odd ({i ∈ (Set.Icc (1 : ℤ) (j + 1) : Set ℤ) | y ∈ G (e i)}.ncard : ℤ)) (Q := y = v (j + 1)) s1_2_12_15 hC4)
  -- 2. def:range0, from H6
  have s2a : 0 ≤ k := by exact (((Parley.Items.Stdlib.Sums.def_range0 (k := k) (n := n) hH2)).mp hH6).1
  have s2b : k ≤ n := by exact (((Parley.Items.Stdlib.Sums.def_range0 (k := k) (n := n) hH2)).mp hH6).2
  -- 3. instantiate j := k in line 1, from 2
  have s3 : ∀ y ∈ V \ ({v (0 : ℤ)} : Set α), Odd ({i ∈ (Set.Icc (1 : ℤ) k : Set ℤ) | y ∈ G (e i)}.ncard : ℤ) ↔ y = v k := by exact (s1 k s2a s2b)
  -- 4. instantiate y := x in line 3, from H7
  exact (s3 x hH7)

end Parley.Tests.Elaborator.InductionUnderACondition.WalkParityByInduction
