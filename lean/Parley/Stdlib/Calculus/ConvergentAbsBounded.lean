module

public import AlgebraTactics
public import ArithTactics
public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sums

/-! Written from corpus/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Calculus.ConvergentAbsBounded

theorem convergent_abs_bounded (x : ℤ → ℝ) (L : ℝ) (hH3 : Filter.Tendsto (fun n : ℤ => (x n : ℝ)) Filter.atTop (nhds L)) :
    (∃ B : ℝ, ∀ m : ℤ, 0 < m → abs (x m) ≤ B) := by
  -- 1. def:tends-to, from H3
  have s1 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (x n - L) < ε)) := by exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := L))).mp hH3
  -- 2. instantiate ε := 1 in line 1
  have r583_1 : (0 : ℤ) < 1 := by parley_arith
  have s2 : ∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (x n - L) < 1) := by exact (s1 (1 : ℝ) (by parley_side))
  -- 3. obtain N from line 2
  obtain ⟨N, s3a, s3b⟩ := s2
  -- 4. mun:first-terms-bounded
  have s4 : ∀ K : ℤ, 0 < K → (∃ C : ℝ, ∀ m : ℤ, m ∈ Finset.Icc 1 K → abs (x m) ≤ C) := by exact (Parley.Items.Stdlib.Calculus.mun_first_terms_bounded (x := x))
  -- 5. instantiate K := N in line 4
  have s5 : ∃ C : ℝ, ∀ i : ℤ, i ∈ Finset.Icc 1 N → abs (x i) ≤ C := by exact (s4 N s3a)
  -- 6. obtain C from line 5
  obtain ⟨C, s6⟩ := s5
  -- 7. membership
  set B : ℝ := max C (abs L + 1) with hD1
  have hD1_kind : True := by trivial
  -- 8. mun:le-max x := C, y := |L| + 1, from D1
  have s8 : C ≤ B := by
    try simp only [hD1] at ⊢
    try push_cast at ⊢
    exact (Parley.Items.Stdlib.Numbers.mun_le_max_1 (x := C) (y := abs L + 1))
  -- 9. mun:le-max x := C, y := |L| + 1, from D1
  have s9 : abs L + 1 ≤ B := by
    try simp only [hD1] at ⊢
    try push_cast at ⊢
    exact (Parley.Items.Stdlib.Numbers.mun_le_max_2 (x := C) (y := abs L + 1))
  -- 10. proof
  have s10 : ∀ m : ℤ, 0 < m → abs (x m) ≤ B := by
    intro m hK1
    -- 10.1. mun:abs-real x := x(m), from H1
    -- 10.2. axi:excluded-middle P := m ≤ N
    have s10_2 : m ≤ N ∨ ¬ m ≤ N := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := m ≤ N))
    -- 10.3. cases, from 10.2
    rcases s10_2 with hC1 | hC2
    · skip
      -- 10.3.1. def:range n := N, k := m, from C1
      have s10_3_1 : m ∈ Finset.Icc (1 : ℤ) N := ((Parley.Items.Stdlib.Sums.def_range (k := m) (n := N))).mpr ⟨hK1, hC1⟩
      -- 10.3.2. instantiate i := m in line 6, from 10.3.1
      have s10_3_2 : abs (x m) ≤ C := by exact (s6 m s10_3_1)
      -- 10.3.3. transitivity, from 10.3.2, 8
      exact le_trans s10_3_2 s8
    · skip
      -- 10.3.4. inequalities, from C2
      have s10_3_4 : N < m := by parley_order
      -- 10.3.5. inequalities
      have s10_3_5 : m ≥ N := by parley_order
      -- 10.3.6. instantiate n := m in line 3, from 10.3.5
      have s10_3_6 : abs (x m - L) < 1 := by exact (s3b m hK1 s10_3_5)
      -- 10.3.7. thm:triangle-inequality a := x(m) − L, b := L
      have s10_3_7 : abs (x m - L + L) ≤ abs (x m - L) + abs L := by exact (Parley.Items.Stdlib.Numbers.thm_triangle_inequality (a := x m - L) (b := L))
      -- 10.3.8. substitute
      have s10_3_8 : abs (x m) ≤ abs (x m - L) + abs L := by
        have c1 : x m - L + L = x m := by parley_ring
        have row1 : abs (x m) ≤ abs (x m - L) + abs L := by (have h := Eq.subst (motive := (fun t : ℝ => abs t ≤ abs (x m - L) + abs L)) c1 s10_3_7; push_cast at h ⊢; all_goals exact_mod_cast h)
        exact row1
      -- 10.3.9. inequalities
      have s10_3_9 : abs (x m - L) + abs L < abs L + 1 := by parley_order
      -- 10.3.10. transitivity, from 10.3.8, 10.3.9
      have s10_3_10 : abs (x m) < abs L + 1 := by exact lt_of_le_of_lt s10_3_8 s10_3_9
      -- 10.3.11. transitivity, from 10.3.10, 9
      have s10_3_11 : abs (x m) < B := by exact lt_of_lt_of_le s10_3_10 s9
      -- 10.3.12. inequalities
      parley_order
  -- 11. exhibit, from 10
  exact ⟨B, s10⟩

end Parley.Stdlib.Calculus.ConvergentAbsBounded
