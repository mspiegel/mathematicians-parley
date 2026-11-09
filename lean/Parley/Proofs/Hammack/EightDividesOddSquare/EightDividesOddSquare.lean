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
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/eight-divides-odd-square.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.EightDividesOddSquare.EightDividesOddSquare

set_option maxHeartbeats 400000 in
theorem eight_divides_odd_square (n : ℤ) (hH2 : Odd n) :
    (8 : ℤ) ∣ n ^ 2 - 1 := by
  -- 1. obtain k: def:odd, from H2
  obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := n))).mp hH2
  -- 2. calculation
  have s2 : n ^ 2 - 1 = 4 * (k * (k + 1)) := by
    calc n ^ 2 - 1 = (2 * k + 1) ^ 2 - 1 := by (have h := congrArg (fun t : ℤ => t ^ 2 - 1) s1; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = 4 * (k * (k + 1)) := by parley_ring
  -- 3. mun:even-or-odd n := k
  have s3 : Even k ∨ Odd k := by exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := k))
  -- 4. cases, from 3
  rcases s3 with hC1 | hC2
  · skip
    -- 4.1. obtain j: def:even n := k, from C1
    obtain ⟨j, s4_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := k))).mp hC1
    -- 4.2. substitute k = 2j (line 4.1) into line 2
    have s4_2 : n ^ 2 - 1 = 4 * (2 * j * (2 * j + 1)) := by (have h := Eq.subst (motive := (fun t : ℤ => n ^ 2 - 1 = 4 * (t * (t + 1)))) s4_1 s2; push_cast at h ⊢; all_goals exact_mod_cast h)
    -- 4.3. calculation
    have s4_3 : n ^ 2 - 1 = 8 * (j * (2 * j + 1)) := by
      calc n ^ 2 - 1 = 4 * (2 * j * (2 * j + 1)) := by exact s4_2
        _ = 8 * (j * (2 * j + 1)) := by parley_ring
    -- 4.4. def:divides d := 8, n := n² − 1, from 4.3
    exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (8 : ℤ)) (n := n ^ 2 - 1))).mpr ⟨j * (2 * j + 1), s4_3⟩
  · skip
    -- 4.5. obtain j: def:odd n := k, from C2
    obtain ⟨j, s4_5⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := k))).mp hC2
    -- 4.6. substitute k = 2j + 1 (line 4.5) into line 2
    have s4_6 : n ^ 2 - 1 = 4 * ((2 * j + 1) * (2 * j + 1 + 1)) := by (have h := Eq.subst (motive := (fun t : ℤ => n ^ 2 - 1 = 4 * (t * (t + 1)))) s4_5 s2; push_cast at h ⊢; all_goals exact_mod_cast h)
    -- 4.7. calculation
    have s4_7 : n ^ 2 - 1 = 8 * ((2 * j + 1) * (j + 1)) := by
      calc n ^ 2 - 1 = 4 * ((2 * j + 1) * (2 * j + 1 + 1)) := by exact s4_6
        _ = 8 * ((2 * j + 1) * (j + 1)) := by parley_ring
    -- 4.8. def:divides d := 8, n := n² − 1, from 4.7
    exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (8 : ℤ)) (n := n ^ 2 - 1))).mpr ⟨(2 * j + 1) * (j + 1), s4_7⟩

end Parley.Proofs.Hammack.EightDividesOddSquare.EightDividesOddSquare
