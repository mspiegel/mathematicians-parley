module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Library

/-! Written from proofs/hammack/divides-sixth-power.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.DividesSixthPower.DividesSixthPower

theorem divides_sixth_power (a : ℤ) (b : ℤ) (c : ℤ) (H4 : a ^ 2 ∣ b) (H5 : b ^ 3 ∣ c) :
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
      _ = a ^ 6 * (k ^ 3 * m) := by ring
  -- 6. def:divides d := a⁶, n := c, from 5
  have s6 : a ^ 6 ∣ c := ((Parley.Items.Stdlib.Divisibility.def_divides (d := a ^ 6) (n := c))).mpr ⟨k ^ 3 * m, by parley_side⟩
  parley_side

end Parley.Proofs.Hammack.DividesSixthPower.DividesSixthPower
