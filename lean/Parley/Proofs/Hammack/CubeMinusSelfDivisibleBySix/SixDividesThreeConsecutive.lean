module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/cube-minus-self-divisible-by-six.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CubeMinusSelfDivisibleBySix.SixDividesThreeConsecutive

theorem six_divides_three_consecutive (k : ℤ) (hH1 : 0 ≤ k) :
    (6 : ℤ) ∣ 3 * k * (k + 1) := by
  -- 1. mun:even-or-odd n := k
  have s1 : Even k ∨ Odd k := by exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := k))
  -- 2. cases, from 1
  rcases s1 with hC1 | hC2
  · skip
    -- 2.1. obtain m: def:even n := k, from C1
    obtain ⟨m, s2_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := k))).mp hC1
    -- 2.2. calculation
    have s2_2 : 3 * k * (k + 1) = 6 * (m * (2 * m + 1)) := by
      calc 3 * k * (k + 1) = 3 * (2 * m) * (2 * m + 1) := by (have h := congrArg (fun t : ℤ => 3 * t * (t + 1)) s2_1; push_cast at h ⊢; all_goals exact_mod_cast h)
        _ = 6 * (m * (2 * m + 1)) := by parley_ring
    -- 2.3. def:divides d := 6, n := 3·k·(k + 1), from 2.2
    exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (6 : ℤ)) (n := 3 * k * (k + 1)))).mpr (by parley_side)
  · skip
    -- 2.4. obtain m: def:odd n := k, from C2
    obtain ⟨m, s2_4⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := k))).mp hC2
    -- 2.5. calculation
    have s2_5 : 3 * k * (k + 1) = 6 * ((2 * m + 1) * (m + 1)) := by
      calc 3 * k * (k + 1) = 3 * (2 * m + 1) * (2 * m + 1 + 1) := by (have h := congrArg (fun t : ℤ => 3 * t * (t + 1)) s2_4; push_cast at h ⊢; all_goals exact_mod_cast h)
        _ = 6 * ((2 * m + 1) * (m + 1)) := by parley_ring
    -- 2.6. def:divides d := 6, n := 3·k·(k + 1), from 2.5
    exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (6 : ℤ)) (n := 3 * k * (k + 1)))).mpr (by parley_side)

end Parley.Proofs.Hammack.CubeMinusSelfDivisibleBySix.SixDividesThreeConsecutive
