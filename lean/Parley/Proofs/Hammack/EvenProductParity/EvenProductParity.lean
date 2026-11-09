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
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/hammack/even-product-parity.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.EvenProductParity.EvenProductParity

set_option maxHeartbeats 400000 in
theorem even_product_parity (x : ℤ) (y : ℤ) (hH3 : Even (x ^ 2 * (y + 3))) :
    (Even x ∨ Odd y) := by
  -- 1. mun:even-or-odd n := x
  have s1 : Even x ∨ Odd x := by exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := x))
  -- 2. cases, from 1
  rcases s1 with hC1 | hC2
  · skip
    -- 2.1. mun:or-left P := x is even, Q := y is odd, from C1
    exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := Even x) (Q := Odd y) hC1)
  · skip
    -- 2.2. mun:even-or-odd n := y
    have s2_2 : Even y ∨ Odd y := by exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := y))
    -- 2.3. cases, from 2.2
    rcases s2_2 with hC3 | hC4
    · skip
      -- 2.3.1. obtain a: def:odd n := x, from C2
      obtain ⟨a, s2_3_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := x))).mp hC2
      -- 2.3.2. obtain b: def:even n := y, from C3
      obtain ⟨b, s2_3_2⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := y))).mp hC3
      -- 2.3.3. calculation
      have s2_3_3 : x ^ 2 * (y + 3) = 2 * (4 * a ^ 2 * b + 6 * a ^ 2 + 4 * a * b + 6 * a + b + 1) + 1 := by
        calc x ^ 2 * (y + 3) = (2 * a + 1) ^ 2 * (y + 3) := by (have h := congrArg (fun t : ℤ => t ^ 2 * (y + 3)) s2_3_1; push_cast at h ⊢; all_goals exact_mod_cast h)
          _ = (2 * a + 1) ^ 2 * (2 * b + 3) := by (have h := congrArg (fun t : ℤ => (2 * a + 1) ^ 2 * (t + 3)) s2_3_2; push_cast at h ⊢; all_goals exact_mod_cast h)
          _ = 2 * (4 * a ^ 2 * b + 6 * a ^ 2 + 4 * a * b + 6 * a + b + 1) + 1 := by parley_ring
      -- 2.3.4. def:odd n := x²·(y + 3), from 2.3.3
      have s2_3_4 : Odd (x ^ 2 * (y + 3)) := ((Parley.Items.Stdlib.Divisibility.def_odd (n := x ^ 2 * (y + 3)))).mpr ⟨4 * a ^ 2 * b + 6 * a ^ 2 + 4 * a * b + 6 * a + b + 1, s2_3_3⟩
      -- 2.3.5. mun:not-both n := x²·(y + 3), from H3
      have s2_3_5 : ¬ Odd (x ^ 2 * (y + 3)) := by exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := x ^ 2 * (y + 3)) hH3)
      exact absurd s2_3_4 s2_3_5
    · skip
      -- 2.3.6. mun:or-right P := x is even, Q := y is odd, from C4
      exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := Even x) (Q := Odd y) hC4)

end Parley.Proofs.Hammack.EvenProductParity.EvenProductParity
