module

public import AlgebraTactics
public import OrderTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Topology.Defs.Filter
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Setmm.LimitLemmas.ScaledSmall

/-! Written from proofs/setmm/limit-constant-multiple.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.LimitConstantMultiple.LimitConstantMultiple

set_option maxHeartbeats 400000 in
theorem limit_constant_multiple (x : ℤ → ℝ) (L : ℝ) (C : ℝ) (hH4 : Filter.Tendsto (fun n : ℤ => (x n : ℝ)) Filter.atTop (nhds L)) :
    Filter.Tendsto (fun n : ℤ => (C * x n : ℝ)) Filter.atTop (nhds (C * L)) := by
  -- 1. mun:abs-nonneg x := C
  have s1 : abs C ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (C : ℂ)))] | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (C : ℂ))); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (C : ℂ))) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (C : ℂ))); parley_side)
  -- 2. inequalities, from 1
  have s2 : abs C + 1 > 0 := by parley_order
  -- 3. inequalities
  have s3 : 2 * (abs C + 1) > 0 := by parley_order
  -- 4. proof
  have s4 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (C * x n - C * L) < ε)) := by
    intro ε
    intro hA1
    -- 4.1. mun:quotient-positive x := ε, y := 2·(|C| + 1), from A1, 3
    have s4_1 : ε / (2 * (abs C + 1)) > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := ε) (y := 2 * (abs C + 1)) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := ε) (y := 2 * (abs C + 1)) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := ε) (y := 2 * (abs C + 1)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := ε) (y := 2 * (abs C + 1)) (by parley_side) (by parley_side)); parley_side)
    -- 4.2. membership
    have r37_1 : 2 * (abs C + 1) ≠ 0 := by parley_side
    -- 4.3. def:tends-to, from H4
    have s4_3 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (x n - L) < ε)) := by first | exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := L))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := L))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := L))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := L))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := x) (L := L))).mp (by parley_side); parley_side)
    -- 4.4. instantiate ε := ε/(2·(|C| + 1)) in line 4.3, from 4.1, 4.2
    have s4_4 : ∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (x n - L) < ε / (2 * (abs C + 1))) := by first | exact (s4_3 (ε / (2 * (abs C + 1))) (by parley_side)) | exact ((s4_3 (ε / (2 * (abs C + 1))) (by parley_side))).symm | simpa using (s4_3 (ε / (2 * (abs C + 1))) (by parley_side)) | exact_mod_cast (s4_3 (ε / (2 * (abs C + 1))) (by parley_side)) | (have h := (s4_3 (ε / (2 * (abs C + 1))) (by parley_side)); parley_side)
    -- 4.5. obtain N from line 4.4
    obtain ⟨N, s4_5a, s4_5b⟩ := s4_4
    -- 4.6. proof
    have s4_6 : ∀ n : ℤ, 0 < n → n ≥ N → abs (C * x n - C * L) < ε := by
      intro n hK2
      intro hA2
      -- 4.6.1. instantiate n := n in line 4.5, from A2
      have s4_6_1 : abs (x n - L) < ε / (2 * (abs C + 1)) := by first | linarith [(s4_5b n (by parley_side) (by parley_side))] | (have h := (s4_5b n (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s4_5b n (by parley_side) (by parley_side)) | (have h := (s4_5b n (by parley_side) (by parley_side)); parley_side)
      -- 4.6.2. membership, from H1
      -- 4.6.3. thm:scaled-small u := x(n) − L, from A1, 4.6.1, 4.6.2
      have s4_6_3 : abs (C * (x n - L)) < ε := by first | linarith [(Parley.Proofs.Setmm.LimitLemmas.ScaledSmall.scaled_small (C := C) (u := x n - L) (ε := ε) hA1 s4_6_1)] | (have h := (Parley.Proofs.Setmm.LimitLemmas.ScaledSmall.scaled_small (C := C) (u := x n - L) (ε := ε) hA1 s4_6_1); push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Setmm.LimitLemmas.ScaledSmall.scaled_small (C := C) (u := x n - L) (ε := ε) hA1 s4_6_1) | (have h := (Parley.Proofs.Setmm.LimitLemmas.ScaledSmall.scaled_small (C := C) (u := x n - L) (ε := ε) hA1 s4_6_1); parley_side)
      -- 4.6.4. substitute
      have s4_6_4 : abs (C * x n - C * L) < ε := by
        have c1 : C * (x n - L) = C * x n - C * L := by parley_ring
        have row1 : abs (C * x n - C * L) < ε := by parley_subst_at c1 s4_6_3
        exact row1
      all_goals parley_side
    -- 4.7. exhibit, from 4.6
    have s4_7 : ∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (C * x n - C * L) < ε) := ⟨N, by parley_side, by parley_side⟩
    all_goals parley_side
  -- 5. def:tends-to L := C·L, from 4
  have s5 : Filter.Tendsto (fun n : ℤ => (C * x n : ℝ)) Filter.atTop (nhds (C * L)) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => C * x n)) (L := C * L))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => C * x n)) (L := C * L))).mpr (by parley_side); parley_side)
  all_goals exact s5

end Parley.Proofs.Setmm.LimitConstantMultiple.LimitConstantMultiple
