module

public import Counting
public import FactorialTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Counting

/-! Written from proofs/setmm/binomial-basics.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.BinomialBasics.FactorialNonzero

theorem factorial_nonzero (N : ℤ) (hH1 : 0 ≤ N) :
    (LeanBridges.Counting.factorial N : ℤ) ≠ 0 := by
  -- 1. mun:factorial-nat n := N
  have s1 : 0 < (LeanBridges.Counting.factorial N : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := N) hH1)
  -- 2. inequalities, from 1
  exact s1.ne'

end Parley.Proofs.Setmm.BinomialBasics.FactorialNonzero
