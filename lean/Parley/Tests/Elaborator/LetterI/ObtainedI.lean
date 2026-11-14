module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/letter-i.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.LetterI.ObtainedI

theorem obtained_i (n : ℤ) (hH2 : Odd n) :
    Odd (n ^ 2) := by
  -- 1. obtain i: def:odd, from H2
  obtain ⟨i, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := n))).mp hH2
  -- 2. substitute n = 2i + 1 (line 1)
  have s2 : n ^ 2 = (2 * i + 1) ^ 2 := congrArg (fun t : ℤ => t ^ 2) s1
  -- 3. algebra
  have s3 : (2 * i + 1) ^ 2 = 2 * (2 * i ^ 2 + 2 * i) + 1 := by ring1
  -- 4. calculation
  have s4 : n ^ 2 = 2 * (2 * i ^ 2 + 2 * i) + 1 := by
    calc n ^ 2 = (2 * i + 1) ^ 2 := s2
      _ = 2 * (2 * i ^ 2 + 2 * i) + 1 := s3
  -- 5. def:odd n := n², from 4
  exact ((Parley.Items.Stdlib.Divisibility.def_odd (n := n ^ 2))).mpr ⟨2 * i ^ 2 + 2 * i, s4⟩

end Parley.Tests.Elaborator.LetterI.ObtainedI
