module

public import AlgebraTactics
public import SubstTactics
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

/-! Written from proofs/hammack/odd-quadratic.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.OddQuadratic.OddQuadratic

theorem odd_quadratic (a : ℤ) (hH2 : Odd a) :
    Odd (a ^ 2 + 3 * a + 5) := by
  -- 1. obtain k: def:odd, from H2
  obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := a))).mp hH2
  -- 2. calculation
  have s2 : a ^ 2 + 3 * a + 5 = 2 * (2 * k ^ 2 + 5 * k + 4) + 1 := by
    calc a ^ 2 + 3 * a + 5 = (2 * k + 1) ^ 2 + 3 * (2 * k + 1) + 5 := by parley_subst s1
      _ = 2 * (2 * k ^ 2 + 5 * k + 4) + 1 := by parley_ring
  -- 3. def:odd n := a² + 3a + 5, from 2
  first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_odd (n := a ^ 2 + 3 * a + 5))).mpr ⟨2 * k ^ 2 + 5 * k + 4, s2⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_odd (n := a ^ 2 + 3 * a + 5))).mpr ⟨2 * k ^ 2 + 5 * k + 4, s2⟩; parley_side)

end Parley.Proofs.Hammack.OddQuadratic.OddQuadratic
