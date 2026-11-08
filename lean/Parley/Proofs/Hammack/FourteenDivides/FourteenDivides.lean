module

public import NormTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/fourteen-divides.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.FourteenDivides.FourteenDivides

set_option maxHeartbeats 400000 in
theorem fourteen_divides (a : ℤ) :
    ((14 : ℤ) ∣ a ↔ (7 : ℤ) ∣ a ∧ (2 : ℤ) ∣ a) := by
  -- the theorem. both directions
  constructor
  · skip
    intro hD1
    -- 1. obtain k: def:divides d := 14, n := a, from D1
    obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (14 : ℤ)) (n := a))).mp hD1
    -- 2. algebra, from 1
    have s2 : a = 7 * (2 * k) := by linear_combination (norm := parley_norm) s1
    -- 3. def:divides d := 7, n := a, from 2
    have s3 : (7 : ℤ) ∣ a := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (7 : ℤ)) (n := a))).mpr ⟨2 * k, s2⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (7 : ℤ)) (n := a))).mpr ⟨2 * k, s2⟩; parley_side)
    -- 4. algebra, from 1
    have s4 : a = 2 * (7 * k) := by linear_combination (norm := parley_norm) s1
    -- 5. def:divides d := 2, n := a, from 4
    have s5 : (2 : ℤ) ∣ a := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := a))).mpr ⟨7 * k, s4⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := a))).mpr ⟨7 * k, s4⟩; parley_side)
    -- 6. join 3, 5
    parley_side
  · skip
    intro hD2
    -- 7. obtain m: def:divides d := 7, n := a, from D2
    obtain ⟨m, s7⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (7 : ℤ)) (n := a))).mp hD2.1
    -- 8. obtain n: def:divides d := 2, n := a, from D2
    obtain ⟨n, s8⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := a))).mp hD2.2
    -- 9. algebra, from 7, 8
    have s9 : a = 14 * (n - 3 * m) := by linear_combination (norm := parley_norm) (-6) * s7 + (7) * s8
    -- 10. def:divides d := 14, n := a, from 9
    first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (14 : ℤ)) (n := a))).mpr ⟨n - 3 * m, s9⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (14 : ℤ)) (n := a))).mpr ⟨n - 3 * m, s9⟩; parley_side)

end Parley.Proofs.Hammack.FourteenDivides.FourteenDivides
