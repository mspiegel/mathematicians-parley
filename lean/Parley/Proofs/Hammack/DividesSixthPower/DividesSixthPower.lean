module

public import AlgebraTactics
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
  obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := a ^ 2) (n := b))).mp hH4
  -- 2. obtain m: def:divides, from H5
  obtain ⟨m, s2⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := b ^ 3) (n := c))).mp hH5
  -- 3. substitute b = a²·k (line 1)
  have s3 : b ^ 3 = (a ^ 2 * k) ^ 3 := by (have h := congrArg (fun t : ℤ => t ^ 3) s1; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 4. substitute b³ = (a²·k)³ (line 3) into line 2
  have s4 : c = (a ^ 2 * k) ^ 3 * m := by (have h := Eq.subst (motive := (fun t : ℤ => c = t * m)) s3 s2; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 5. calculation
  have s5 : c = a ^ 6 * (k ^ 3 * m) := by
    calc c = (a ^ 2 * k) ^ 3 * m := by exact s4
      _ = a ^ 6 * (k ^ 3 * m) := by parley_ring
  -- 6. def:divides d := a⁶, n := c, from 5
  exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := a ^ 6) (n := c))).mpr ⟨k ^ 3 * m, s5⟩

end Parley.Proofs.Hammack.DividesSixthPower.DividesSixthPower
