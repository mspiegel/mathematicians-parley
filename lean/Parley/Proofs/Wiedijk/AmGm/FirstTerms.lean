module

public import SetTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/wiedijk/am-gm.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.AmGm.FirstTerms

theorem first_terms (n : ℤ) (hH1 : 0 < n) (a : ℤ → ℝ) (hH3 : ∀ k : ℤ, k ∈ Finset.Icc 1 n → a k ≥ 0) (m : ℤ) (hH5 : m ≤ n) :
    True ∧ (∀ k : ℤ, k ∈ Finset.Icc 1 m → a k ≥ 0) := by
  -- 1. mun:range-within a := 1, from H5
  have s1 : (Set.Icc (1 : ℤ) m : Set ℤ) ⊆ (Set.Icc (1 : ℤ) n : Set ℤ) := by exact (Parley.Items.Stdlib.Sums.mun_range_within (a := (1 : ℤ)) (k := m) (n := n) hH5)
  -- 2. proof
  -- what this block shows, Lean's types give
  -- 3. proof
  have s3 : ∀ k : ℤ, k ∈ Finset.Icc 1 m → a k ≥ 0 := by
    intro k hK2
    try push_cast at hK2
    try have hK2_bounds := Finset.mem_Icc.mp hK2
    -- 3.1. instantiate k := k in H3, from 1
    exact (hH3 k (by parley_set_side))
  -- 4. join 2, 3
  have s4 : ∀ k : ℤ, k ∈ Finset.Icc 1 m → a k ≥ 0 := by intro k h_k; parley_set_side
  exact ⟨trivial, s4⟩

end Parley.Proofs.Wiedijk.AmGm.FirstTerms
