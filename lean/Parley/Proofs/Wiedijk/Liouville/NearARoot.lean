module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning
public import Parley.Proofs.Wiedijk.Liouville.MeanValueBound

/-! Written from proofs/wiedijk/liouville.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Liouville.NearARoot

theorem near_a_root (f : ℝ → ℝ) (hH2 : ContinuousOn f (Set.univ : Set ℝ)) (hH3 : ∀ x ∈ (Set.univ : Set ℝ), (Set.univ : Set ℝ) ∈ nhds x ∧ DifferentiableAt ℝ f x) (α : ℝ) (hH5 : f α = 0) (K : ℝ) (hH7 : K > 0) (hH8 : ∀ t ∈ (Set.Icc (α - 1) (α + 1) : Set ℝ), abs ((deriv f) t) ≤ K) (x : ℝ) (hH10 : abs (α - x) ≤ 1) :
    abs (f x) ≤ K * abs (α - x) := by
  -- 1. mun:abs-difference-le x := α, c := x, δ := 1, from H10
  have s1 : x - 1 ≤ α ∧ α ≤ x + 1 := by exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_le (x := α) (c := x) (δ := (1 : ℝ)))).mp hH10
  -- 2. inequalities, from 1
  have s2 : α - 1 ≤ x := by linarith only [s1.2]
  -- 3. inequalities, from 1
  have s3 : x ≤ α + 1 := by linarith only [s1.1]
  -- 4. proof
  have s4 : ∀ t ∈ (Set.Icc x α : Set ℝ), abs ((deriv f) t) ≤ K := by
    intro t hK1
    -- 4.1. def:interval a := x, b := α, x := t, from K1
    have s4_1 : (True ∧ x ≤ t) ∧ t ≤ α := by exact ((Parley.Items.Stdlib.Calculus.def_interval (x := t) (a := x) (b := α))).mp hK1
    -- 4.2. transitivity, from 2, 4.1
    have s4_2 : α - 1 ≤ t := by exact le_trans s2 s4_1.1.2
    -- 4.3. inequalities, from 4.1
    have s4_3 : t ≤ α + 1 := by linarith only [s4_1.2]
    -- 4.4. def:interval a := α − 1, b := α + 1, x := t
    have r274_1 : α - 1 ≤ t := by exact s4_2
    have r274_2 : t ≤ α + 1 := by exact s4_3
    have s4_4 : t ∈ (Set.Icc (α - 1) (α + 1) : Set ℝ) := ((Parley.Items.Stdlib.Calculus.def_interval (x := t) (a := α - 1) (b := α + 1))).mpr ⟨⟨by trivial, r274_1⟩, r274_2⟩
    -- 4.5. instantiate t := t in H8, from 4.4
    exact (hH8 t s4_4)
  -- 5. proof
  have s5 : ∀ t ∈ (Set.Icc α x : Set ℝ), abs ((deriv f) t) ≤ K := by
    intro t hK2
    -- 5.1. def:interval a := α, b := x, x := t, from K2
    have s5_1 : (True ∧ α ≤ t) ∧ t ≤ x := by exact ((Parley.Items.Stdlib.Calculus.def_interval (x := t) (a := α) (b := x))).mp hK2
    -- 5.2. inequalities, from 5.1
    have s5_2 : α - 1 ≤ t := by linarith only [s5_1.1.2]
    -- 5.3. transitivity, from 5.1, 3
    have s5_3 : t ≤ α + 1 := by exact le_trans s5_1.2 s3
    -- 5.4. def:interval a := α − 1, b := α + 1, x := t
    have r295_1 : α - 1 ≤ t := by exact s5_2
    have r295_2 : t ≤ α + 1 := by exact s5_3
    have s5_4 : t ∈ (Set.Icc (α - 1) (α + 1) : Set ℝ) := ((Parley.Items.Stdlib.Calculus.def_interval (x := t) (a := α - 1) (b := α + 1))).mpr ⟨⟨by trivial, r295_1⟩, r295_2⟩
    -- 5.5. instantiate t := t in H8, from 5.4
    exact (hH8 t s5_4)
  -- 6. axi:excluded-middle
  have s6 : x = α ∨ x ≠ α := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := x = α))
  -- 7. cases, from 6
  rcases s6 with hC1 | hC2
  · skip
    -- 7.1. substitute x = α (C1) into H5
    have s7_1 : f x = 0 := Eq.subst (motive := (fun t : ℝ => f t = 0)) hC1.symm hH5
    -- 7.2. substitute f(x) = 0 (line 7.1)
    have s7_2 : abs (f x) = abs 0 := congrArg (fun t : ℝ => abs t) s7_1
    -- 7.3. mun:abs-zero
    have s7_3 : (abs 0 : ℤ) = 0 := by exact Parley.Items.Stdlib.Numbers.mun_abs_zero
    -- 7.4. mun:abs-nonneg x := α − x
    have s7_4 : abs (α - x) ≥ 0 := by
      have hI : 0 ≤ abs (α - x) := by exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (α : ℂ) - (x : ℂ))))
      exact hI
    -- 7.5. mun:product-nonneg x := K, y := |α − x|, from 7.4
    have r324_1 : K ≥ 0 := by linarith only [hH7]
    have s7_5 : K * abs (α - x) ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := K) (y := abs (α - x)) r324_1 s7_4)
    -- 7.6. transitivity, from 7.2, 7.3, 7.5
    exact Eq.trans_le (Eq.trans s7_2 (show (abs 0 : ℝ) = 0 by exact_mod_cast s7_3)) s7_5
  · skip
    -- 7.7. mun:unequal-cases y := α, from C2
    have s7_7 : x < α ∨ α < x := by exact ((Parley.Items.Stdlib.Numbers.mun_unequal_cases (x := x) (y := α))).mp hC2
    -- 7.8. cases, from 7.7
    rcases s7_7 with hC3 | hC4
    · skip
      -- 7.8.1. thm:mean-value-bound a := x, b := α, M := K, from C3, H2, H3, 4
      have s7_8_1 : abs (f α - f x) ≤ K * (α - x) := by exact (Parley.Proofs.Wiedijk.Liouville.MeanValueBound.mean_value_bound (f := f) hH2 hH3 (a := x) (b := α) hC3 (M := K) s4)
      -- 7.8.2. algebra, from H5
      have s7_8_2 : f α - f x = -f x := by linear_combination hH5
      -- 7.8.3. substitute f(α) − f(x) = −f(x) (line 7.8.2)
      have s7_8_3 : abs (f α - f x) = abs (-f x) := congrArg (fun t : ℝ => abs t) s7_8_2
      -- 7.8.4. mun:abs-negative x := f(x)
      have s7_8_4 : abs (-f x) = abs (f x) := by exact (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := f x))
      -- 7.8.5. inequalities
      have s7_8_5 : α - x ≥ 0 := by linarith only [hC3]
      -- 7.8.6. def:abs x := α − x, from 7.8.5
      have s7_8_6 : abs (α - x) = α - x := by exact (Parley.Items.Stdlib.Numbers.def_abs_1 (x := α - x)) s7_8_5
      -- 7.8.7. substitute |α − x| = α − x (line 7.8.6)
      have s7_8_7 : K * (α - x) = K * abs (α - x) := congrArg (fun t : ℝ => K * t) s7_8_6.symm
      -- 7.8.8. transitivity, from 7.8.4, 7.8.3, 7.8.1, 7.8.7
      exact LE.le.trans_eq (Eq.trans_le (Eq.trans s7_8_4.symm s7_8_3.symm) s7_8_1) s7_8_7
    · skip
      -- 7.8.9. thm:mean-value-bound a := α, b := x, M := K, from C4, H2, H3, 5
      have s7_8_9 : abs (f x - f α) ≤ K * (x - α) := by exact (Parley.Proofs.Wiedijk.Liouville.MeanValueBound.mean_value_bound (f := f) hH2 hH3 (a := α) (b := x) hC4 (M := K) s5)
      -- 7.8.10. algebra, from H5
      have s7_8_10 : f x - f α = f x := by linear_combination (-1) * hH5
      -- 7.8.11. substitute f(x) − f(α) = f(x) (line 7.8.10)
      have s7_8_11 : abs (f x - f α) = abs (f x) := congrArg (fun t : ℝ => abs t) s7_8_10
      -- 7.8.12. inequalities
      have s7_8_12 : α - x < 0 := by linarith only [hC4]
      -- 7.8.13. def:abs x := α − x, from 7.8.12
      have s7_8_13 : abs (α - x) = -(α - x) := by exact (Parley.Items.Stdlib.Numbers.def_abs_2 (x := α - x)) s7_8_12
      -- 7.8.14. algebra
      have s7_8_14 : x - α = -(α - x) := by ring1
      -- 7.8.15. substitute x − α = −(α − x) (line 7.8.14)
      have s7_8_15 : K * (x - α) = K * -(α - x) := congrArg (fun t : ℝ => K * t) s7_8_14
      -- 7.8.16. substitute |α − x| = −(α − x) (line 7.8.13)
      have s7_8_16 : K * -(α - x) = K * abs (α - x) := congrArg (fun t : ℝ => K * t) s7_8_13.symm
      -- 7.8.17. transitivity, from 7.8.11, 7.8.9, 7.8.15, 7.8.16
      exact LE.le.trans_eq (LE.le.trans_eq (Eq.trans_le s7_8_11.symm s7_8_9) s7_8_15) s7_8_16

end Parley.Proofs.Wiedijk.Liouville.NearARoot
