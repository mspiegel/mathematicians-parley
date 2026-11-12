module

public import AlgebraTactics
public import InstanceTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Basic.Complex.Basic
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
public import Parley.Proofs.Setmm.LimitLemmas.ScaledSmall

/-! Written from proofs/setmm/limit-constant-multiple.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.LimitConstantMultiple.LimitConstantMultiple

theorem limit_constant_multiple (x : ℤ → ℝ) (L : ℝ) (C : ℝ) (hH4 : Filter.Tendsto (fun n : ℤ => (x n : ℝ)) Filter.atTop (nhds L)) :
    Filter.Tendsto (fun n : ℤ => (C * x n : ℝ)) Filter.atTop (nhds (C * L)) := by
  -- 1. mun:abs-nonneg x := C
  have s1 : abs C ≥ 0 := by
    have hI : 0 ≤ abs C := by parley_instance_cast ((Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (C : ℂ))))
    exact hI
  -- 2. inequalities, from 1
  have s2 : abs C + 1 > 0 := by linarith only [s1]
  -- 3. inequalities
  have s3 : 2 * (abs C + 1) > 0 := by linarith only [s2]
  -- 4. proof
  have s4 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (C * x n - C * L) < ε)) := by
    intro ε
    intro hA1
    -- 4.1. mun:quotient-positive x := ε, y := 2·(|C| + 1), from A1, 3
    have s4_1 : ε / (2 * (abs C + 1)) > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := ε) (y := 2 * (abs C + 1)) hA1 s3)
    -- 4.2. membership
    have r37_1 : 2 * (abs C + 1) ≠ 0 := ne_of_gt (by linarith only [s3])
    -- 4.3. def:tends-to, from H4
    have s4_3 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (x n - L) < ε)) := by exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := L))).mp hH4
    -- 4.4. instantiate ε := ε/(2·(|C| + 1)) in line 4.3, from 4.1, 4.2
    have s4_4 : ∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (x n - L) < ε / (2 * (abs C + 1))) := by exact (s4_3 (ε / (2 * (abs C + 1))) s4_1)
    -- 4.5. obtain N from line 4.4
    obtain ⟨N, s4_5a, s4_5b⟩ := s4_4
    -- 4.6. proof
    have s4_6 : ∀ n : ℤ, 0 < n → n ≥ N → abs (C * x n - C * L) < ε := by
      intro n hK2
      intro hA2
      -- 4.6.1. instantiate n := n in line 4.5, from A2
      have s4_6_1 : abs (x n - L) < ε / (2 * (abs C + 1)) := by exact (s4_5b n hK2 hA2)
      -- 4.6.2. membership, from H1
      -- 4.6.3. thm:scaled-small u := x(n) − L, from A1, 4.6.1, 4.6.2
      have s4_6_3 : abs (C * (x n - L)) < ε := by exact (Parley.Proofs.Setmm.LimitLemmas.ScaledSmall.scaled_small (C := C) (u := x n - L) (ε := ε) (by parley_side) s4_6_1)
      -- 4.6.4. substitute
      have c1 : C * (x n - L) = C * x n - C * L := by parley_ring
      have row1 : abs (C * x n - C * L) < ε := by (have h := Eq.subst (motive := (fun t : ℝ => abs t < ε)) c1 s4_6_3; push_cast at h ⊢; all_goals exact_mod_cast h)
      exact row1
    -- 4.7. exhibit, from 4.6
    exact ⟨N, s4_5a, s4_6⟩
  -- 5. def:tends-to L := C·L, from 4
  exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => C * x n)) (L := C * L))).mpr s4

end Parley.Proofs.Setmm.LimitConstantMultiple.LimitConstantMultiple
