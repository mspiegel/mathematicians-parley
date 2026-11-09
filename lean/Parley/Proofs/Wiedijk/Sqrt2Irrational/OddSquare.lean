module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/wiedijk/sqrt2-irrational.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Sqrt2Irrational.OddSquare

theorem odd_square (n : ℤ) (hH2 : Odd n) :
    Odd (n ^ 2) := by
  -- 1. obtain k: def:odd, from H2
  obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := n))).mp hH2
  -- 2. calculation
  have s2 : n ^ 2 = 2 * (2 * k ^ 2 + 2 * k) + 1 := by
    calc n ^ 2 = (2 * k + 1) ^ 2 := by (have h := congrArg (fun t : ℤ => t ^ 2) s1; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = 4 * k ^ 2 + 4 * k + 1 := by parley_ring
      _ = 2 * (2 * k ^ 2 + 2 * k) + 1 := by parley_ring
  -- 3. def:odd n := n², from 2
  exact ((Parley.Items.Stdlib.Divisibility.def_odd (n := n ^ 2))).mpr ⟨2 * k ^ 2 + 2 * k, s2⟩

end Parley.Proofs.Wiedijk.Sqrt2Irrational.OddSquare
