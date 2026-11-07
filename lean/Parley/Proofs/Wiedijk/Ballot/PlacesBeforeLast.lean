module

public import OrderTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/wiedijk/ballot.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Ballot.PlacesBeforeLast

theorem places_before_last (p : ℤ) (N : ℤ) (hH3 : 1 ≤ p) (hH4 : p + 1 = N) :
    (Set.Icc (1 : ℤ) p : Set ℤ) = (Set.Icc (1 : ℤ) N : Set ℤ) \ ({N} : Set ℤ) := by
  -- 1. inequalities, from H3
  have s1 : 0 < p := by parley_order
  -- 2. mun:pos-int-nat m := p, from 1
  have s2 : 0 < p := by exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := p) s1)
  -- 3. mun:range-without-last n := p, from 2
  have s3 : (Set.Icc (1 : ℤ) p : Set ℤ) = (Set.Icc (1 : ℤ) (p + 1) : Set ℤ) \ ({p + 1} : Set ℤ) := by exact (Parley.Items.Stdlib.Sums.mun_range_without_last (n := p) (by parley_set_side))
  -- 4. substitute p + 1 = N (H4) into line 3
  have s4 : (Set.Icc (1 : ℤ) p : Set ℤ) = (Set.Icc (1 : ℤ) N : Set ℤ) \ ({N} : Set ℤ) := by parley_subst_at hH4 s3
  all_goals exact s4

end Parley.Proofs.Wiedijk.Ballot.PlacesBeforeLast
