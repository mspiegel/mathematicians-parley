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
public import Mathlib.Order.Basic
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

/-! Written from proofs/hammack/constant-multiple-limit.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ConstantMultipleLimit.ConstantMultipleLimit

theorem constant_multiple_limit (a : ℤ → ℝ) (c : ℝ) (L : ℝ) (hH4 : Filter.Tendsto (fun n : ℤ => (a n : ℝ)) Filter.atTop (nhds L)) :
    Filter.Tendsto (fun n : ℤ => (c * a n : ℝ)) Filter.atTop (nhds (c * L)) := by
  -- 1. mun:abs-nonneg x := c
  have s1 : abs c ≥ 0 := by
    have hI : 0 ≤ abs c := by parley_instance_cast ((Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (c : ℂ))))
    exact hI
  -- 2. inequalities, from 1
  have s2 : abs c + 1 > 0 := by linarith only [s1]
  -- 3. inequalities
  have s3 : abs c + 1 ≠ 0 := ne_of_gt (by linarith only [s2])
  -- 4. proof
  have s4 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (c * a n - c * L) < ε)) := by
    intro ε
    intro hA1
    -- 4.1. mun:quotient-positive x := ε, y := |c| + 1, from A1, 2
    have s4_1 : ε / (abs c + 1) > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := ε) (y := abs c + 1) hA1 s2)
    -- 4.2. membership
    have r39_1 : abs c + 1 ≠ 0 := by exact s3
    -- 4.3. def:tends-to, from H4
    have s4_3 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (a n - L) < ε)) := by exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := L))).mp hH4
    -- 4.4. instantiate ε := ε/(|c| + 1) in line 4.3, from 4.1, 4.2
    have s4_4 : ∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (a n - L) < ε / (abs c + 1)) := by exact (s4_3 (ε / (abs c + 1)) s4_1)
    -- 4.5. obtain N from line 4.4
    obtain ⟨N, s4_5a, s4_5b⟩ := s4_4
    -- 4.6. proof
    have s4_6 : ∀ n : ℤ, 0 < n → n ≥ N → abs (c * a n - c * L) < ε := by
      intro n hK2
      intro hA2
      -- 4.6.1. membership, from H1
      -- 4.6.2. mun:abs-real x := a(n) − L, from 4.6.1
      -- 4.6.3. instantiate n := n in line 4.5, from A2
      have s4_6_3 : abs (a n - L) < ε / (abs c + 1) := by exact (s4_5b n hK2 hA2)
      -- 4.6.4. mun:abs-nonneg x := a(n) − L, from 4.6.1
      have s4_6_4 : abs (a n - L) ≥ 0 := by
        have hI : 0 ≤ abs (a n - L) := by parley_instance_cast ((Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (a n : ℂ) - (L : ℂ))))
        exact hI
      -- 4.6.5. mun:less-scaled x := |a(n) − L|, y := ε/(|c| + 1), c := |c| + 1, from 2, 4.6.2, 4.6.3
      have s4_6_5 : (abs c + 1) * abs (a n - L) < (abs c + 1) * (ε / (abs c + 1)) := by exact ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := abs (a n - L)) (y := ε / (abs c + 1)) (c := abs c + 1) s2)).mp s4_6_3
      -- 4.6.6. algebra
      have r72_1 : abs c + 1 ≠ 0 := by exact s3
      have s4_6_6 : (abs c + 1) * (ε / (abs c + 1)) = ε := by parley_ring
      -- 4.6.7. algebra, from 4.6.2
      have s4_6_7 : (abs c + 1) * abs (a n - L) = abs c * abs (a n - L) + abs (a n - L) := by parley_ring
      -- 4.6.8. mun:abs-product x := c, y := a(n) − L, from 4.6.1
      have s4_6_8 : abs (c * (a n - L)) = abs c * abs (a n - L) := by exact (Parley.Items.Stdlib.Numbers.mun_abs_product (x := c) (y := a n - L))
      -- 4.6.9. substitute
      have s4_6_9 : abs (c * a n - c * L) = abs c * abs (a n - L) := by
        have c1 : c * (a n - L) = c * a n - c * L := by parley_ring
        have row1 : abs (c * a n - c * L) = abs c * abs (a n - L) := by (have h := Eq.subst (motive := (fun t : ℝ => abs t = abs c * abs (a n - L))) c1 s4_6_8; push_cast at h ⊢; all_goals exact_mod_cast h)
        exact row1
      -- 4.6.10. inequalities
      have s4_6_10 : abs c * abs (a n - L) ≤ abs c * abs (a n - L) + abs (a n - L) := by linarith only [s4_6_4]
      -- 4.6.11. transitivity, from 4.6.9, 4.6.10, 4.6.7, 4.6.5, 4.6.6
      have r95_2 : abs c + 1 ≠ 0 := by exact s3
      exact LT.lt.trans_eq (lt_of_le_of_lt (LE.le.trans_eq (Eq.trans_le s4_6_9 s4_6_10) s4_6_7.symm) s4_6_5) s4_6_6
    -- 4.7. exhibit, from 4.6
    exact ⟨N, s4_5a, s4_6⟩
  -- 5. def:tends-to L := c·L, from 4
  exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => c * a n)) (L := c * L))).mpr s4

end Parley.Proofs.Hammack.ConstantMultipleLimit.ConstantMultipleLimit
