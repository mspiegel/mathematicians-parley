module

public import AlgebraTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/divides-square-difference.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.DividesSquareDifference.DividesSquareDifference

theorem divides_square_difference (a : ℤ) (b : ℤ) (c : ℤ) (hH4 : a ∣ b) (hH5 : a ∣ b ^ 2 - c) :
    a ∣ c := by
  -- 1. mun:divides-multiple e := a, a := b, x := b, from H4
  have s1 : a ∣ b * b := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := a) (a := b) (x := b) hH4)
  -- 2. substitute
  have s2 : a ∣ b ^ 2 := by
    have c1 : b * b = b ^ 2 := by parley_ring
    have row1 : a ∣ b ^ 2 := by parley_subst_at c1 s1
    exact row1
  -- 3. mun:divides-difference d := a, a := b², b := b² − c, from H5, 2
  have s3 : a ∣ b ^ 2 - (b ^ 2 - c) := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := a) (a := b ^ 2) (b := b ^ 2 - c) s2 hH5)
  -- 4. substitute
  have s4 : a ∣ c := by
    have c1 : b ^ 2 - (b ^ 2 - c) = c := by parley_ring
    have row1 : a ∣ c := by parley_subst_at c1 s3
    exact row1
  all_goals exact s4

end Parley.Proofs.Hammack.DividesSquareDifference.DividesSquareDifference
