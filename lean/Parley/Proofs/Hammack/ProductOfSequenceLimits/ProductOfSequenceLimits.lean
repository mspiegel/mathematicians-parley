module

public import AlgebraTactics
public import ArithTactics
public import OrderTactics
public import RealTactics
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
public import Mathlib.Tactic.Set
public import Mathlib.Topology.Defs.Filter
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Hammack.ProductOfSequenceLimits.BoundedTimesSmall
public import Parley.Proofs.Wiedijk.TriangleInequality.TriangleInequality

/-! Written from proofs/hammack/product-of-sequence-limits.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ProductOfSequenceLimits.ProductOfSequenceLimits

set_option maxHeartbeats 1000000 in
theorem product_of_sequence_limits (a : ℤ → ℝ) (b : ℤ → ℝ) (L : ℝ) (M : ℝ) (hH5 : Filter.Tendsto (fun n : ℤ => (a n : ℝ)) Filter.atTop (nhds L)) (hH6 : Filter.Tendsto (fun n : ℤ => (b n : ℝ)) Filter.atTop (nhds M)) :
    Filter.Tendsto (fun n : ℤ => (a n * b n : ℝ)) Filter.atTop (nhds (L * M)) := by
  -- 1. mun:abs-real x := L
  -- 2. mun:abs-nonneg x := L
  have s2 : abs L ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (L : ℂ)))] | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (L : ℂ))); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (L : ℂ))) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (L : ℂ))); parley_side)
  set s : ℝ := abs L + 1 with hD1
  have hD1_kind : True := by first | exact (Parley.Items.Stdlib.Numbers.mun_real_closure_1 (x := abs L) (y := (1 : ℝ))) | exact ((Parley.Items.Stdlib.Numbers.mun_real_closure_1 (x := abs L) (y := (1 : ℝ)))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_real_closure_1 (x := abs L) (y := (1 : ℝ))) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_real_closure_1 (x := abs L) (y := (1 : ℝ))) | (have h := (Parley.Items.Stdlib.Numbers.mun_real_closure_1 (x := abs L) (y := (1 : ℝ))); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Numbers.mun_real_closure_1 (x := abs L) (y := (1 : ℝ))); parley_side)
  -- 3. inequalities, from D1, 2
  have s3 : s > 0 := by parley_order
  -- 4. mun:abs-real x := M
  -- 5. mun:abs-nonneg x := M
  have s5 : abs M ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (M : ℂ)))] | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (M : ℂ))); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (M : ℂ))) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (M : ℂ))); parley_side)
  set t : ℝ := abs M + 1 with hD2
  have hD2_kind : True := by first | exact (Parley.Items.Stdlib.Numbers.mun_real_closure_1 (x := abs M) (y := (1 : ℝ))) | exact ((Parley.Items.Stdlib.Numbers.mun_real_closure_1 (x := abs M) (y := (1 : ℝ)))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_real_closure_1 (x := abs M) (y := (1 : ℝ))) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_real_closure_1 (x := abs M) (y := (1 : ℝ))) | (have h := (Parley.Items.Stdlib.Numbers.mun_real_closure_1 (x := abs M) (y := (1 : ℝ))); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Numbers.mun_real_closure_1 (x := abs M) (y := (1 : ℝ))); parley_side)
  -- 6. inequalities, from D2, 5
  have s6 : t > 0 := by parley_order
  -- 7. inequalities
  have s7 : abs M < abs M + 1 := by parley_order
  -- 8. substitute t = |M| + 1 (D2) into line 7
  have s8 : abs M < t := by parley_subst_at hD2 s7
  -- 9. proof
  have s9 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (a n * b n - L * M) < ε)) := by
    intro ε
    intro hA1
    -- 9.1. inequalities
    have s9_1 : 2 * s > 0 := by parley_order
    -- 9.2. inequalities
    have s9_2 : 2 * s ≠ 0 := by parley_side
    -- 9.3. mun:quotient-positive x := ε, y := 2·s, from A1, 9.1
    have s9_3 : ε / (2 * s) > 0 := (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := ε) (y := 2 * s) (by parley_side) (by parley_side))
    -- 9.4. inequalities
    have s9_4 : 2 * t > 0 := by parley_order
    -- 9.5. inequalities
    have s9_5 : 2 * t ≠ 0 := by parley_side
    -- 9.6. mun:quotient-positive x := ε, y := 2·t, from A1, 9.4
    have s9_6 : ε / (2 * t) > 0 := (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := ε) (y := 2 * t) (by parley_side) (by parley_side))
    -- 9.7. mun:quotient-real x := ε, y := 2·t, from 9.5
    set m : ℝ := min 1 (ε / (2 * t)) with hD3
    have hD3_kind : True := by first | exact (Parley.Items.Stdlib.Numbers.mun_min_real (x := (1 : ℝ)) (y := ε / (2 * t))) | exact ((Parley.Items.Stdlib.Numbers.mun_min_real (x := (1 : ℝ)) (y := ε / (2 * t)))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_min_real (x := (1 : ℝ)) (y := ε / (2 * t))) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_min_real (x := (1 : ℝ)) (y := ε / (2 * t))) | (have h := (Parley.Items.Stdlib.Numbers.mun_min_real (x := (1 : ℝ)) (y := ε / (2 * t))); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Numbers.mun_min_real (x := (1 : ℝ)) (y := ε / (2 * t))); parley_side)
    -- 9.8. mun:lt-min z := 0, x := 1, y := ε/(2·t), from 9.6, 9.7
    have r148_1 : (0 : ℤ) < 1 := by parley_arith
    have s9_8 : 0 < min 1 (ε / (2 * t)) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_lt_min (z := (0 : ℝ)) (x := (1 : ℝ)) (y := ε / (2 * t)))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_lt_min (z := (0 : ℝ)) (x := (1 : ℝ)) (y := ε / (2 * t)))).mpr (by parley_side); parley_side)
    -- 9.9. inequalities, from D3, 9.8
    have s9_9 : m > 0 := by parley_order
    -- 9.10. def:tends-to x := a, from H5
    have s9_10 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (a n - L) < ε)) := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := a) (L := L))).mp hH5
    -- 9.11. def:tends-to x := b, L := M, from H6
    have s9_11 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (b n - M) < ε)) := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := b) (L := M))).mp hH6
    -- 9.12. instantiate ε := m in line 9.10, from 9.9
    have s9_12 : ∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (a n - L) < m) := by first | exact (s9_10 m (by parley_side)) | exact ((s9_10 m (by parley_side))).symm | simpa using (s9_10 m (by parley_side)) | exact_mod_cast (s9_10 m (by parley_side)) | (have h := (s9_10 m (by parley_side)); parley_side)
    -- 9.13. instantiate ε := ε/(2·s) in line 9.11, from 9.3
    have s9_13 : ∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (b n - M) < ε / (2 * s)) := by first | exact (s9_11 (ε / (2 * s)) (by parley_side)) | exact ((s9_11 (ε / (2 * s)) (by parley_side))).symm | simpa using (s9_11 (ε / (2 * s)) (by parley_side)) | exact_mod_cast (s9_11 (ε / (2 * s)) (by parley_side)) | (have h := (s9_11 (ε / (2 * s)) (by parley_side)); parley_side)
    -- 9.14. obtain P from line 9.12
    obtain ⟨P, s9_14a, s9_14b⟩ := s9_12
    -- 9.15. obtain Q from line 9.13
    obtain ⟨Q, s9_15a, s9_15b⟩ := s9_13
    -- 9.16. inequalities, from 9.15
    have s9_16 : Q > 0 := by parley_order
    -- 9.17. inequalities
    have s9_17 : P + Q ≥ P := by parley_order
    -- 9.18. inequalities, from 9.14
    have s9_18 : P > 0 := by parley_order
    -- 9.19. inequalities
    have s9_19 : P + Q ≥ Q := by parley_order
    -- 9.20. proof
    have s9_20 : ∀ n : ℤ, 0 < n → n ≥ P + Q → abs (a n * b n - L * M) < ε := by
      intro n hK2
      intro hA2
      -- 9.20.1. transitivity, from A2, 9.17
      have s9_20_1 : n ≥ P := by parley_order
      -- 9.20.2. transitivity, from A2, 9.19
      have s9_20_2 : n ≥ Q := by parley_order
      -- 9.20.3. instantiate n := n in line 9.14, from 9.20.1
      have s9_20_3 : abs (a n - L) < m := by first | linarith [(s9_14b n (by parley_side) (by parley_side))] | (have h := (s9_14b n (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s9_14b n (by parley_side) (by parley_side)) | (have h := (s9_14b n (by parley_side) (by parley_side)); parley_side)
      -- 9.20.4. instantiate n := n in line 9.15, from 9.20.2
      have s9_20_4 : abs (b n - M) < ε / (2 * s) := by first | linarith [(s9_15b n (by parley_side) (by parley_side))] | (have h := (s9_15b n (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s9_15b n (by parley_side) (by parley_side)) | (have h := (s9_15b n (by parley_side) (by parley_side)); parley_side)
      -- 9.20.5. mun:lt-min z := |a(n) − L|, x := 1, y := ε/(2·t), from D3, 9.20.3
      have s9_20_5 : abs (a n - L) < 1 ∧ abs (a n - L) < ε / (2 * t) := by
        try simp only [hD3] at *
        try push_cast at *
        exact ((Parley.Items.Stdlib.Numbers.mun_lt_min (z := abs (a n - L)) (x := (1 : ℝ)) (y := ε / (2 * t)))).mp s9_20_3
      -- 9.20.6. algebra
      have s9_20_6 : a n - L + L = a n := by parley_ring
      -- 9.20.7. calculation
      have s9_20_7 : abs (a n) ≤ abs (a n - L) + abs L := by
        calc abs (a n) = abs (a n - L + L) := by parley_subst s9_20_6
          _ ≤ abs (a n - L) + abs L := by exact (Parley.Proofs.Wiedijk.TriangleInequality.TriangleInequality.triangle_inequality (a := a n - L) (b := L))
      -- 9.20.8. inequalities
      have s9_20_8 : abs (a n - L) + abs L < abs L + 1 := by parley_order
      -- 9.20.9. transitivity, from 9.20.7, 9.20.8
      have s9_20_9 : abs (a n) < abs L + 1 := by parley_order
      -- 9.20.10. substitute s = |L| + 1 (D1) into line 9.20.9
      have s9_20_10 : abs (a n) < s := by parley_subst_at hD1 s9_20_9
      -- 9.20.11. calculation
      have r238_3 : 2 * s ≠ 0 := by parley_side
      have s9_20_11 : abs (a n * (b n - M)) < ε / 2 := by
        calc abs (a n * (b n - M)) < s * (ε / (2 * s)) := by exact (Parley.Proofs.Hammack.ProductOfSequenceLimits.BoundedTimesSmall.bounded_times_small (C := a n) (u := b n - M) (K := s) (d := ε / (2 * s)) (by parley_side) s9_20_10 s9_20_4)
          _ = ε / 2 := by parley_ring
      -- 9.20.12. calculation
      have r246_2 : 2 * t ≠ 0 := by parley_side
      have s9_20_12 : abs (M * (a n - L)) < ε / 2 := by
        calc abs (M * (a n - L)) < t * (ε / (2 * t)) := by exact (Parley.Proofs.Hammack.ProductOfSequenceLimits.BoundedTimesSmall.bounded_times_small (C := M) (u := a n - L) (K := t) (d := ε / (2 * t)) (by parley_side) s8 s9_20_5.2)
          _ = ε / 2 := by parley_ring
      -- 9.20.13. algebra
      have s9_20_13 : a n * b n - L * M = a n * (b n - M) + M * (a n - L) := by parley_ring
      -- 9.20.14. inequalities, from 9.20.11, 9.20.12
      have s9_20_14 : abs (a n * (b n - M)) + abs (M * (a n - L)) < ε / 2 + ε / 2 := by parley_order
      -- 9.20.15. calculation
      calc abs (a n * b n - L * M) = abs (a n * (b n - M) + M * (a n - L)) := by parley_subst s9_20_13
        _ ≤ abs (a n * (b n - M)) + abs (M * (a n - L)) := by exact (Parley.Proofs.Wiedijk.TriangleInequality.TriangleInequality.triangle_inequality (a := a n * (b n - M)) (b := M * (a n - L)))
        _ < ε / 2 + ε / 2 := by parley_side
        _ = ε := by parley_ring
    -- 9.21. exhibit, from 9.20
    exact ⟨P + Q, by parley_side, s9_20⟩
  -- 10. def:tends-to L := L·M, from 9
  first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => a n * b n)) (L := L * M))).mpr s9 | (have h := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => a n * b n)) (L := L * M))).mpr s9; parley_side)

end Parley.Proofs.Hammack.ProductOfSequenceLimits.ProductOfSequenceLimits
