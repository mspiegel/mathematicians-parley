module

public import AlgebraTactics
public import ArithTactics
public import NormTactics
public import SetTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/square-limit.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SquareLimit.SquareLimit

theorem square_limit (f : ℝ → ℝ) (hH2 : ∀ x : ℝ, f x = x ^ 2 - 2) :
    Filter.Tendsto f (nhdsWithin 3 ((Set.univ : Set ℝ) \ {3})) (nhds 7) := by
  -- 1. proof
  have s1 : ∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ (∀ x : ℝ, x ≠ 3 ∧ abs (x - 3) < δ → abs (f x - 7) < ε)) := by
    intro ε
    intro hA1
    set m : ℝ := min 1 (ε / 7) with hD1
    -- 1.1. inequalities
    have s1_1 : 0 < ε / 7 := by linarith only [hA1]
    -- 1.2. mun:lt-min z := 0, x := 1, y := ε/7
    have r36_1 : (0 : ℤ) < 1 := by parley_arith
    have r36_2 : 0 < ε / 7 := by exact s1_1
    have s1_2 : 0 < min 1 (ε / 7) := ((Parley.Items.Stdlib.Numbers.mun_lt_min (z := (0 : ℝ)) (x := (1 : ℝ)) (y := ε / 7))).mpr ⟨by norm_num, r36_2⟩
    -- 1.3. inequalities, from D1, 1.2
    have s1_3 : m > 0 := by linarith only [s1_2, hD1]
    -- 1.4. proof
    have s1_4 : ∀ x : ℝ, x ≠ 3 ∧ abs (x - 3) < m → abs (f x - 7) < ε := by
      intro x
      intro hA2
      -- 1.4.1. mun:lt-min z := |x − 3|, x := 1, y := ε/7, from A2, D1
      have s1_4_1 : abs (x - 3) < 1 ∧ abs (x - 3) < ε / 7 := by
        try simp only [hD1] at ⊢
        try push_cast at ⊢
        exact ((Parley.Items.Stdlib.Numbers.mun_lt_min (z := abs (x - 3)) (x := (1 : ℝ)) (y := ε / 7))).mp hA2.2
      -- 1.4.2. mun:abs-difference-lt c := 3, δ := 1, from 1.4.1
      have s1_4_2 : 3 - 1 < x ∧ x < 3 + 1 := by exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x) (c := (3 : ℝ)) (δ := (1 : ℝ)))).mp s1_4_1.1
      -- 1.4.3. inequalities, from 1.4.2
      have s1_4_3 : x + 3 > 0 := by linarith only [s1_4_2.1]
      -- 1.4.4. inequalities
      have s1_4_4 : x + 3 ≥ 0 := by linarith only [s1_4_3]
      -- 1.4.5. def:abs x := x + 3, from 1.4.4
      have s1_4_5 : abs (x + 3) = x + 3 := by exact (Parley.Items.Stdlib.Numbers.def_abs_1 (x := x + 3)) s1_4_4
      -- 1.4.6. inequalities, from 1.4.2
      have s1_4_6 : x + 3 < 7 := by linarith only [s1_4_2.2]
      -- 1.4.7. transitivity, from 1.4.3, 1.4.5
      have s1_4_7 : 0 < abs (x + 3) := by exact LT.lt.trans_eq s1_4_3 s1_4_5.symm
      -- 1.4.8. transitivity, from 1.4.5, 1.4.6
      have s1_4_8 : abs (x + 3) < 7 := by exact Eq.trans_lt s1_4_5 s1_4_6
      -- 1.4.9. join 1.4.7, 1.4.8
      have s1_4_9 : 0 < abs (x + 3) ∧ abs (x + 3) < 7 := ⟨s1_4_7, s1_4_8⟩
      -- 1.4.10. inequalities
      have s1_4_10 : abs (x + 3) ≤ 7 := by linarith only [s1_4_8]
      -- 1.4.11. instantiate x := x in H2
      have s1_4_11 : f x = x ^ 2 - 2 := by exact (hH2 x)
      -- 1.4.12. mun:abs-product x := x + 3, y := x − 3
      have s1_4_12 : abs ((x + 3) * (x - 3)) = abs (x + 3) * abs (x - 3) := by exact (Parley.Items.Stdlib.Numbers.mun_abs_product (x := x + 3) (y := x - 3))
      -- 1.4.13. substitute
      have s1_4_13 : abs (f x - 7) = abs (x + 3) * abs (x - 3) := by
        have c1 : (x + 3) * (x - 3) = f x - 7 := by linear_combination (norm := parley_norm) (-1) * s1_4_11
        have row1 : abs (f x - 7) = abs (x + 3) * abs (x - 3) := by (have h := Eq.subst (motive := (fun t : ℝ => abs t = abs (x + 3) * abs (x - 3))) c1 s1_4_12; push_cast at h ⊢; all_goals exact_mod_cast h)
        exact row1
      -- 1.4.14. calculation
      have r94_1 : ε / 7 > 0 := by linarith only [hA1]
      calc abs (f x - 7) = abs (x + 3) * abs (x - 3) := s1_4_13
        _ < abs (x + 3) * (ε / 7) := by exact ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := abs (x - 3)) (y := ε / 7) (c := abs (x + 3)) s1_4_9.1)).mp s1_4_1.2
        _ = ε / 7 * abs (x + 3) := by parley_ring
        _ ≤ ε / 7 * 7 := by exact (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := abs (x + 3)) (y := (7 : ℝ)) (c := ε / 7) s1_4_10 r94_1)
        _ = ε := by parley_ring
    -- 1.5. exhibit, from 1.3, 1.4
    exact ⟨m, ⟨s1_3, s1_4⟩⟩
  -- 2. def:limit-at D := ℝ, c := 3, L := 7, from 1
  have r106_1 : (Set.univ : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ)))
  exact ((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := (Set.univ : Set ℝ)) r106_1 (c := (3 : ℝ)) (L := (7 : ℝ)))).mpr (by simpa only [gt_iff_lt, Set.mem_univ, forall_const] using s1)

end Parley.Proofs.Hammack.SquareLimit.SquareLimit
