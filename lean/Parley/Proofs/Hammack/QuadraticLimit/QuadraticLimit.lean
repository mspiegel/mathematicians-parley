module

public import AlgebraTactics
public import ArithTactics
public import NormTactics
public import OrderTactics
public import RealTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import WholeTactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Filter
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/quadratic-limit.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.QuadraticLimit.QuadraticLimit

set_option maxHeartbeats 600000 in
theorem quadratic_limit (f : ℝ → ℝ) (hH2 : ∀ x : ℝ, f x = 4 * x ^ 2 + 1) :
    Filter.Tendsto f (nhdsWithin 1 ((Set.univ : Set ℝ) \ {1})) (nhds 5) := by
  -- 1. proof
  have s1 : ∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ (∀ x : ℝ, x ≠ 1 ∧ abs (x - 1) < δ → abs (f x - 5) < ε)) := by
    intro ε
    intro hA1
    set m : ℝ := min 1 (ε / 12) with hD1
    have hD1_kind : True := by first | exact (Parley.Items.Stdlib.Numbers.mun_min_real (x := (1 : ℝ)) (y := ε / 12)) | exact ((Parley.Items.Stdlib.Numbers.mun_min_real (x := (1 : ℝ)) (y := ε / 12))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_min_real (x := (1 : ℝ)) (y := ε / 12)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_min_real (x := (1 : ℝ)) (y := ε / 12)) | (have h := (Parley.Items.Stdlib.Numbers.mun_min_real (x := (1 : ℝ)) (y := ε / 12)); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Numbers.mun_min_real (x := (1 : ℝ)) (y := ε / 12)); parley_set_side)
    -- 1.1. inequalities
    have s1_1 : 0 < ε / 12 := by parley_order
    -- 1.2. mun:lt-min z := 0, x := 1, y := ε/12
    have r36_1 : (0 : ℤ) < 1 := by parley_arith
    have r36_2 : 0 < ε / 12 := by parley_set_side
    have s1_2 : 0 < min 1 (ε / 12) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_lt_min (z := (0 : ℝ)) (x := (1 : ℝ)) (y := ε / 12))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_lt_min (z := (0 : ℝ)) (x := (1 : ℝ)) (y := ε / 12))).mpr (by parley_set_side); parley_set_side)
    -- 1.3. inequalities, from D1, 1.2
    have s1_3 : m > 0 := by parley_order
    -- 1.4. proof
    have s1_4 : ∀ x : ℝ, x ≠ 1 ∧ abs (x - 1) < m → abs (f x - 5) < ε := by
      intro x
      intro hA2
      -- 1.4.1. mun:lt-min z := |x − 1|, x := 1, y := ε/12, from A2, D1
      have s1_4_1 : abs (x - 1) < 1 ∧ abs (x - 1) < ε / 12 := by
        try simp only [hD1] at *
        try push_cast at *
        exact ((Parley.Items.Stdlib.Numbers.mun_lt_min (z := abs (x - 1)) (x := (1 : ℝ)) (y := ε / 12))).mp hA2.2
      -- 1.4.2. mun:abs-difference-lt c := 1, δ := 1, from 1.4.1
      have s1_4_2 : 1 - 1 < x ∧ x < 1 + 1 := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x) (c := (1 : ℝ)) (δ := (1 : ℝ)))).mp s1_4_1.1
      -- 1.4.3. inequalities
      have s1_4_3 : 4 * x > 0 := by parley_order
      -- 1.4.4. inequalities, from 1.4.3
      have s1_4_4 : 4 * x + 4 > 0 := by parley_order
      -- 1.4.5. def:abs x := 4·x + 4
      have r64_1 : 4 * x + 4 ≥ 0 := by parley_set_side
      have s1_4_5 : abs (4 * x + 4) = 4 * x + 4 := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := 4 * x + 4)) (by parley_set_side)
      -- 1.4.6. inequalities
      have s1_4_6 : 4 * x + 4 < 12 := by parley_order
      -- 1.4.7. transitivity, from 1.4.4, 1.4.5
      have s1_4_7 : 0 < abs (4 * x + 4) := by parley_order
      -- 1.4.8. transitivity, from 1.4.5, 1.4.6
      have s1_4_8 : abs (4 * x + 4) < 12 := by parley_order
      -- 1.4.9. join 1.4.7, 1.4.8
      have s1_4_9 : 0 < abs (4 * x + 4) ∧ abs (4 * x + 4) < 12 := by parley_set_side
      -- 1.4.10. inequalities
      have s1_4_10 : abs (4 * x + 4) ≤ 12 := by parley_order
      -- 1.4.11. instantiate x := x in H2
      have s1_4_11 : f x = 4 * x ^ 2 + 1 := by exact (hH2 x)
      -- 1.4.12. mun:abs-product x := 4·x + 4, y := x − 1
      have s1_4_12 : abs ((4 * x + 4) * (x - 1)) = abs (4 * x + 4) * abs (x - 1) := by exact (Parley.Items.Stdlib.Numbers.mun_abs_product (x := 4 * x + 4) (y := x - 1))
      -- 1.4.13. substitute
      have s1_4_13 : abs (f x - 5) = abs (4 * x + 4) * abs (x - 1) := by
        have c1 : (4 * x + 4) * (x - 1) = f x - 5 := by linear_combination (norm := parley_norm) (-1) * s1_4_11
        have row1 : abs (f x - 5) = abs (4 * x + 4) * abs (x - 1) := by parley_subst_at c1 s1_4_12
        exact row1
      -- 1.4.14. calculation
      have r99_1 : ε / 12 > 0 := by parley_set_side
      calc abs (f x - 5) = abs (4 * x + 4) * abs (x - 1) := by parley_set_side
        _ < abs (4 * x + 4) * (ε / 12) := ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := abs (x - 1)) (y := ε / 12) (c := abs (4 * x + 4)) (by parley_set_side))).mp s1_4_1.2
        _ = ε / 12 * abs (4 * x + 4) := by parley_ring
        _ ≤ ε / 12 * 12 := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := abs (4 * x + 4)) (y := (12 : ℝ)) (c := ε / 12) (by parley_set_side) (by parley_set_side))
        _ = ε := by parley_ring
    -- 1.5. exhibit, from 1.3, 1.4
    exact ⟨m, ⟨s1_3, s1_4⟩⟩
  -- 2. def:limit-at D := ℝ, c := 1, L := 5, from 1
  have r111_1 : (Set.univ : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ)))
  first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := (Set.univ : Set ℝ)) (by parley_whole_side) (c := (1 : ℝ)) (L := (5 : ℝ)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := (Set.univ : Set ℝ)) (by parley_whole_side) (c := (1 : ℝ)) (L := (5 : ℝ)))).mpr (by parley_set_side); parley_set_side)

end Parley.Proofs.Hammack.QuadraticLimit.QuadraticLimit
