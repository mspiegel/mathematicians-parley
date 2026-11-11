module

public import NormTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sets
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/wiedijk/ballot.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Ballot.LastPlace

theorem last_place (m : ℤ) (hH1 : 0 ≤ m) (n : ℤ) (hH2 : 0 ≤ n) (c : Set ℤ) (hH3 : c ⊆ (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (hH4 : (c.ncard : ℤ) = m) :
    (((Set.Icc (1 : ℤ) (m + n) : Set ℤ) \ c).ncard : ℤ) = n ∧ (((Set.Icc (1 : ℤ) (m + n) : Set ℤ) ∩ c).ncard : ℤ) = m := by
  -- 1. mun:range-finite a := 1, b := m + n
  have s1 : (Set.Icc (1 : ℤ) (m + n) : Set ℤ).Finite := by exact (Parley.Items.Stdlib.Sums.mun_range_finite (a := (1 : ℤ)) (b := m + n))
  -- 2. mun:card-difference X := {1, …, m + n}, Y := c, from H3, 1
  have s2 : (((Set.Icc (1 : ℤ) (m + n) : Set ℤ) \ c).ncard : ℤ) = ((Set.Icc (1 : ℤ) (m + n) : Set ℤ).ncard : ℤ) - (c.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_difference (X := (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (Y := c) s1 hH3)
  -- 3. mun:range-size n := m + n
  have s3 : ((Set.Icc (1 : ℤ) (m + n) : Set ℤ).ncard : ℤ) = m + n := by exact (Parley.Items.Stdlib.Counting.mun_range_size (n := m + n) (by parley_set_side))
  -- 4. algebra, from H4, 2, 3
  have s4 : (((Set.Icc (1 : ℤ) (m + n) : Set ℤ) \ c).ncard : ℤ) = n := by parley_count_int; (linear_combination (norm := parley_norm) (-1) * hH4 + s2 + s3)
  -- 5. mun:intersection-of-part X := {1, …, m + n}, Y := c, from H3
  have s5 : (Set.Icc (1 : ℤ) (m + n) : Set ℤ) ∩ c = c := by exact (Parley.Items.Stdlib.Sets.mun_intersection_of_part (X := (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (Y := c) hH3)
  -- 6. calculation
  have s6 : (((Set.Icc (1 : ℤ) (m + n) : Set ℤ) ∩ c).ncard : ℤ) = m := by parley_count_after (by
    calc (((Set.Icc (1 : ℤ) (m + n) : Set ℤ) ∩ c).ncard : ℤ) = (c.ncard : ℤ) := by parley_subst s5
      _ = m := by parley_set_side)
  -- 7. join 4, 6
  have s7a : (((Set.Icc (1 : ℤ) (m + n) : Set ℤ) \ c).ncard : ℤ) = n := by parley_set_side
  have s7b : (((Set.Icc (1 : ℤ) (m + n) : Set ℤ) ∩ c).ncard : ℤ) = m := by parley_set_side
  exact ⟨s7a, s7b⟩

end Parley.Proofs.Wiedijk.Ballot.LastPlace
