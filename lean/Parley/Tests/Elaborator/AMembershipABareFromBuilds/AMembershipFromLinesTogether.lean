module

public import Counting
public import FactorialTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Counting

/-! Written from tests/elaborator/a-membership-a-bare-from-builds.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AMembershipABareFromBuilds.AMembershipFromLinesTogether

theorem a_membership_from_lines_together (k : ℤ) (hH2 : 0 ≤ k) (y : ℝ) (hH4 : y ≤ (LeanBridges.Counting.factorial (k + 1) : ℝ)) (hH5 : (LeanBridges.Counting.factorial (k + 1) : ℤ) ≤ 3) :
    y ≤ 3 := by
  -- 1. mun:factorial-nat n := k, from H2
  have s1 : 0 < (LeanBridges.Counting.factorial k : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := k) hH2)
  -- 2. def:factorial n := k, from H2
  have s2 : (LeanBridges.Counting.factorial (k + 1) : ℤ) = (LeanBridges.Counting.factorial k : ℤ) * (k + 1) := by exact (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k) hH2)
  -- 3. transitivity, from H4, H5
  exact le_trans hH4 (show (LeanBridges.Counting.factorial (k + 1) : ℝ) ≤ 3 by exact_mod_cast hH5)

end Parley.Tests.Elaborator.AMembershipABareFromBuilds.AMembershipFromLinesTogether
