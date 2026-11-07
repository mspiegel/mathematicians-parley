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

/-! Written from proofs/hammack/divides-sixth-power.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.DividesSixthPower.DividesSixthPower

theorem divides_sixth_power (a : ℤ) (b : ℤ) (c : ℤ) (hH4 : a ^ 2 ∣ b) (hH5 : b ^ 3 ∣ c) :
    a ^ 6 ∣ c := by
  -- 1. obtain k: def:divides, from H4
  obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := a ^ 2) (n := b))).mp (by parley_side)
  -- 2. obtain m: def:divides, from H5
  obtain ⟨m, s2⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := b ^ 3) (n := c))).mp (by parley_side)
  -- 3. substitute b = a²·k (line 1)
  have s3 : b ^ 3 = (a ^ 2 * k) ^ 3 := by parley_subst s1
  -- 4. substitute b³ = (a²·k)³ (line 3) into line 2
  have s4 : c = (a ^ 2 * k) ^ 3 * m := by parley_subst_at s3 s2
  -- 5. calculation
  have s5 : c = a ^ 6 * (k ^ 3 * m) := by
    calc c = (a ^ 2 * k) ^ 3 * m := by parley_side
      _ = a ^ 6 * (k ^ 3 * m) := by parley_ring
  -- 6. def:divides d := a⁶, n := c, from 5
  have s6 : a ^ 6 ∣ c := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := a ^ 6) (n := c))).mpr ⟨k ^ 3 * m, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := a ^ 6) (n := c))).mpr ⟨k ^ 3 * m, by parley_side⟩; parley_side)
  all_goals exact s6

end Parley.Proofs.Hammack.DividesSixthPower.DividesSixthPower
