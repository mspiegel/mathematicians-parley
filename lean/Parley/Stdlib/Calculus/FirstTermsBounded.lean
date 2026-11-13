module

public import Functions
public import Tactics
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums

/-! Written from corpus/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Calculus.FirstTermsBounded

theorem first_terms_bounded (x : ℤ → ℝ) :
    (∀ K : ℤ, 0 < K → (∃ C : ℝ, ∀ m : ℤ, m ∈ Finset.Icc 1 K → abs (x m) ≤ C)) := by
  -- 1. induction on K starting at 1
  intro K h_K
  replace h_K : 1 ≤ K := by omega
  induction K, h_K using LeanBridges.Functions.le_induction with
  | base =>
    -- 1.1. mun:abs-real x := x(1)
    -- 1.2. proof
    have s1_2 : ∀ m : ℤ, m ∈ Finset.Icc 1 1 → abs (x m) ≤ abs (x 1) := by
      intro m hK1
      try push_cast at hK1
      try have hK1_bounds := Finset.mem_Icc.mp hK1
      -- 1.2.1. def:range n := 1, k := m, from K1
      have s1_2_1 : 0 < m ∧ m ≤ 1 := by exact ((Parley.Items.Stdlib.Sums.def_range (k := m) (n := (1 : ℤ)))).mp hK1
      -- 1.2.2. inequalities, from 1.2.1
      have s1_2_2 : m ≤ 1 := by linarith only [s1_2_1.2]
      -- 1.2.3. inequalities, from K1
      have s1_2_3 : 1 ≤ m := by linarith only [(Finset.mem_Icc.mp hK1).1]
      -- 1.2.4. antisymmetry, from 1.2.2, 1.2.3
      have s1_2_4 : m = 1 := le_antisymm s1_2_2 s1_2_3
      -- 1.2.5. substitute m = 1 (line 1.2.4)
      have s1_2_5 : abs (x m) = abs (x 1) := by (have h := congrArg (fun t : ℤ => abs (x t)) s1_2_4; push_cast at h ⊢; all_goals exact_mod_cast h)
      -- 1.2.6. inequalities
      linarith only [s1_2_5]
    -- 1.3. exhibit, from 1.1, 1.2
    exact ⟨abs (x 1), s1_2⟩
  | succ K hK hIH =>
    -- 1.4. obtain C from IH
    obtain ⟨C, s1_4⟩ := hIH
    -- 1.5. mun:abs-real x := x(K + 1)
    set E : ℝ := max C (abs (x (K + 1))) with hD
    -- 1.6. mun:le-max x := C, y := |x(K + 1)|, from D, 1.5
    have s1_6 : C ≤ E := by
      try simp only [hD] at ⊢
      try push_cast at ⊢
      exact (Parley.Items.Stdlib.Numbers.mun_le_max_1 (x := C) (y := abs (x (K + 1))))
    -- 1.7. mun:le-max x := C, y := |x(K + 1)|, from D, 1.5
    have s1_7 : abs (x (K + 1)) ≤ E := by
      try simp only [hD] at ⊢
      try push_cast at ⊢
      exact (Parley.Items.Stdlib.Numbers.mun_le_max_2 (x := C) (y := abs (x (K + 1))))
    -- 1.8. proof
    have s1_8 : ∀ m : ℤ, m ∈ Finset.Icc 1 (K + 1) → abs (x m) ≤ E := by
      intro m hK2
      try push_cast at hK2
      try have hK2_bounds := Finset.mem_Icc.mp hK2
      -- 1.8.1. def:range n := K + 1, k := m, from K2
      have s1_8_1 : 0 < m ∧ m ≤ K + 1 := by exact ((Parley.Items.Stdlib.Sums.def_range (k := m) (n := K + 1))).mp hK2
      -- 1.8.2. mun:le-cases x := m, y := K + 1, from 1.8.1
      have s1_8_2 : m < K + 1 ∨ m = K + 1 := by exact ((Parley.Items.Stdlib.Numbers.mun_le_cases (x := m) (y := K + 1))).mp s1_8_1.2
      -- 1.8.3. mun:abs-real x := x(m), from H1
      -- 1.8.4. cases, from 1.8.2
      rcases s1_8_2 with hC1 | hC2
      · skip
        -- 1.8.4.1. mun:integer-step n := K + 1, from C1
        have s1_8_4_1 : m + 1 ≤ K + 1 := by exact (Parley.Items.Stdlib.Numbers.mun_integer_step (m := m) (n := K + 1) hC1)
        -- 1.8.4.2. inequalities
        have s1_8_4_2 : m ≤ K := by linarith only [s1_8_4_1]
        -- 1.8.4.3. def:range n := K, k := m, from 1.8.4.2
        have s1_8_4_3 : m ∈ Finset.Icc (1 : ℤ) K := ((Parley.Items.Stdlib.Sums.def_range (k := m) (n := K))).mpr ⟨lt_of_lt_of_le (by norm_num) (Finset.mem_Icc.mp hK2).1, s1_8_4_2⟩
        -- 1.8.4.4. instantiate i := m in line 1.4, from 1.8.4.3
        have s1_8_4_4 : abs (x m) ≤ C := by exact (s1_4 m s1_8_4_3)
        -- 1.8.4.5. transitivity, from 1.8.4.4, 1.6
        exact le_trans s1_8_4_4 s1_6
      · skip
        -- 1.8.4.6. substitute m = K + 1 (C2)
        have s1_8_4_6 : abs (x m) = abs (x (K + 1)) := by (have h := congrArg (fun t : ℤ => abs (x t)) hC2; push_cast at h ⊢; all_goals exact_mod_cast h)
        -- 1.8.4.7. transitivity, from 1.8.4.6, 1.7
        exact Eq.trans_le s1_8_4_6 s1_7
    -- 1.9. exhibit, from 1.8
    exact ⟨E, s1_8⟩

end Parley.Stdlib.Calculus.FirstTermsBounded
