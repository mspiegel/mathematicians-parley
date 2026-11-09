module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.Group.Even
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

/-! Written from proofs/hammack/quadratic-plus-four-even.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.QuadraticPlusFourEven.QuadraticPlusFourEven

theorem quadratic_plus_four_even (n : ℤ) :
    Even (n ^ 2 + 3 * n + 4) := by
  -- 1. mun:even-or-odd
  have s1 : Even n ∨ Odd n := by exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := n))
  -- 2. cases, from 1
  rcases s1 with hC1 | hC2
  · skip
    -- 2.1. obtain k: def:even, from C1
    obtain ⟨k, s2_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := n))).mp hC1
    -- 2.2. calculation
    have s2_2 : n ^ 2 + 3 * n + 4 = 2 * (2 * k ^ 2 + 3 * k + 2) := by
      calc n ^ 2 + 3 * n + 4 = (2 * k) ^ 2 + 3 * (2 * k) + 4 := by (have h := congrArg (fun t : ℤ => t ^ 2 + 3 * t + 4) s2_1; push_cast at h ⊢; all_goals exact_mod_cast h)
        _ = 2 * (2 * k ^ 2 + 3 * k + 2) := by parley_ring
    -- 2.3. def:even n := n² + 3n + 4, from 2.2
    exact ((Parley.Items.Stdlib.Divisibility.def_even (n := n ^ 2 + 3 * n + 4))).mpr ⟨2 * k ^ 2 + 3 * k + 2, s2_2⟩
  · skip
    -- 2.4. obtain k: def:odd, from C2
    obtain ⟨k, s2_4⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := n))).mp hC2
    -- 2.5. calculation
    have s2_5 : n ^ 2 + 3 * n + 4 = 2 * (2 * k ^ 2 + 5 * k + 4) := by
      calc n ^ 2 + 3 * n + 4 = (2 * k + 1) ^ 2 + 3 * (2 * k + 1) + 4 := by (have h := congrArg (fun t : ℤ => t ^ 2 + 3 * t + 4) s2_4; push_cast at h ⊢; all_goals exact_mod_cast h)
        _ = 2 * (2 * k ^ 2 + 5 * k + 4) := by parley_ring
    -- 2.6. def:even n := n² + 3n + 4, from 2.5
    exact ((Parley.Items.Stdlib.Divisibility.def_even (n := n ^ 2 + 3 * n + 4))).mpr ⟨2 * k ^ 2 + 5 * k + 4, s2_5⟩

end Parley.Proofs.Hammack.QuadraticPlusFourEven.QuadraticPlusFourEven
