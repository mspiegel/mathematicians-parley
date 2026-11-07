module

public import Counting
public import FactorialTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Wiedijk.LiouvilleNumber.TermsReal

/-! Written from proofs/wiedijk/liouville-number.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumReal

theorem partial_sum_real (m : ℤ) (hH1 : 0 < m) :
    True := by
  -- 1. D0, from H1
  have s1 : (∑ k ∈ Finset.Icc (1 : ℤ) m, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) = (∑ k ∈ Finset.Icc (1 : ℤ) m, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) := by parley_side
  -- 2. thm:terms-real
  -- 3. mun:sum-real a := 1, b := m, from 2
  -- 4. substitute Σ(k = 1 to m) 1/2^(k!) = s(m) (line 1) into line 3
  all_goals parley_side

end Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumReal
