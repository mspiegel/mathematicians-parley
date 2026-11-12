module

public import AlgebraTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers

/-! Written from corpus/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Calculus.LimitAtLeast

theorem limit_at_least (x : ℤ → ℝ) (L : ℝ) (hH3 : Filter.Tendsto (fun n : ℤ => (x n : ℝ)) Filter.atTop (nhds L)) (B : ℝ) (N : ℤ) (hH5 : 0 < N) (hH6 : ∀ n : ℤ, 0 < n → n ≥ N → B ≤ x n) :
    B ≤ L := by
  -- the theorem. contradiction
  by_contra hS
  -- 1. inequalities, from S
  have s1 : L < B := by linarith only [hS]
  -- 2. inequalities
  have s2 : B - L > 0 := by linarith only [s1]
  -- 3. def:tends-to, from H3
  have s3 : ∀ ε : ℝ, ε > 0 → (∃ M : ℤ, 0 < M ∧ (∀ n : ℤ, 0 < n → n ≥ M → abs (x n - L) < ε)) := by exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := L))).mp hH3
  -- 4. instantiate ε := B − L in line 3, from 2
  have s4 : ∃ M : ℤ, 0 < M ∧ (∀ n : ℤ, 0 < n → n ≥ M → abs (x n - L) < B - L) := by exact (s3 (B - L) s2)
  -- 5. obtain M from line 4
  obtain ⟨M, s5a, s5b⟩ := s4
  -- 6. inequalities, from H5
  have s6 : M + N ≥ M := by linarith only [hH5]
  -- 7. inequalities, from 5
  have s7 : M + N ≥ N := by linarith only [s5a]
  -- 8. instantiate n := M + N in line 5, from 6
  have s8 : abs (x (M + N) - L) < B - L := by exact (s5b (M + N) (add_pos (s5a) (hH5)) s6)
  -- 9. instantiate n := M + N in H6, from 7
  have s9 : B ≤ x (M + N) := by exact (hH6 (M + N) (add_pos (s5a) (hH5)) s7)
  -- 10. membership, from H1
  -- 11. mun:abs-difference-lt x := x(M + N), c := L, δ := B − L, from 8, 10
  have s11 : L - (B - L) < x (M + N) ∧ x (M + N) < L + (B - L) := by exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x (M + N)) (c := L) (δ := B - L))).mp s8
  -- 12. inequalities, from 10, 11
  have s12 : x (M + N) < L + (B - L) := by linarith only [s11.2]
  -- 13. substitute
  have s13 : x (M + N) < B := by
    have c1 : L + (B - L) = B := by parley_ring
    have row1 : x (M + N) < B := by (have h := Eq.subst (motive := (fun t : ℝ => x (M + N) < t)) c1 s12; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact row1
  -- 14. inequalities, from 10, 13
  have s14 : ¬ B ≤ x (M + N) := by linarith only [s13]
  exact s14 s9

end Parley.Stdlib.Calculus.LimitAtLeast
