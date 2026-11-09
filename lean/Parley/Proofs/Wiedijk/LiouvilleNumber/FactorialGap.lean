module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import Functions
public import OrderTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/wiedijk/liouville-number.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.LiouvilleNumber.FactorialGap

theorem factorial_gap (n : ℤ) (hH1 : 0 < n) :
    (∀ j : ℤ, 0 ≤ j → (LeanBridges.Counting.factorial (n + 1) : ℤ) + j ≤ (LeanBridges.Counting.factorial (n + 1 + j) : ℤ)) := by
  -- the theorem. induction on j starting at 0
  intro j h_j
  replace h_j : 0 ≤ j := by omega
  induction j, h_j using LeanBridges.Functions.le_induction with
  | base =>
    -- 1. inequalities
    have s1 : (LeanBridges.Counting.factorial (n + 1) : ℤ) ≤ (LeanBridges.Counting.factorial (n + 1) : ℤ) := by parley_order
    simpa only [add_zero] using s1
  | succ j hK hIH =>
    -- 2. algebra
    have s2 : n + 1 + j + 1 = n + 1 + (j + 1) := by parley_ring
    -- 3. mun:factorial-nat n := n + 1 + j
    have s3 : 0 < (LeanBridges.Counting.factorial (n + 1 + j) : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := n + 1 + j) (by parley_side))
    -- 4. algebra
    have s4 : (LeanBridges.Counting.factorial (n + 1 + j) : ℤ) * (n + 1 + j + 1) = (n + 1 + j + 1) * (LeanBridges.Counting.factorial (n + 1 + j) : ℤ) := by parley_ring
    -- 5. inequalities, from IH, 3
    have s5 : (LeanBridges.Counting.factorial (n + 1) : ℤ) + (j + 1) ≤ 2 * (LeanBridges.Counting.factorial (n + 1 + j) : ℤ) := by parley_order
    -- 6. calculation
    have r66_1 : 2 ≤ n + 1 + j + 1 := by parley_order
    have r66_2 : (LeanBridges.Counting.factorial (n + 1 + j) : ℤ) ≥ 0 := by parley_order
    calc (LeanBridges.Counting.factorial (n + 1) : ℤ) + (j + 1) ≤ 2 * (LeanBridges.Counting.factorial (n + 1 + j) : ℤ) := by exact s5
      _ ≤ (n + 1 + j + 1) * (LeanBridges.Counting.factorial (n + 1 + j) : ℤ) := by exact (Parley.Items.Stdlib.Numbers.mun_multiply_le_nonneg (x := (2 : ℤ)) (y := n + 1 + j + 1) (c := (LeanBridges.Counting.factorial (n + 1 + j) : ℤ)) (by parley_side) (by parley_side))
      _ = (LeanBridges.Counting.factorial (n + 1 + j) : ℤ) * (n + 1 + j + 1) := by exact s4.symm
      _ = (LeanBridges.Counting.factorial (n + 1 + j + 1) : ℤ) := by exact (Parley.Items.Stdlib.Counting.def_factorial_3 (n := n + 1 + j) (by parley_side)).symm
      _ = (LeanBridges.Counting.factorial (n + 1 + (j + 1)) : ℤ) := by parley_subst s2

end Parley.Proofs.Wiedijk.LiouvilleNumber.FactorialGap
