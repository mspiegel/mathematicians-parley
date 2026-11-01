module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Library

/-! Written from proofs/hammack/fourteen-divides.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.FourteenDivides.FourteenDivides

theorem fourteen_divides (a : ℤ) :
    ((14 : ℤ) ∣ a ↔ (7 : ℤ) ∣ a ∧ (2 : ℤ) ∣ a) := by
  -- the theorem. both directions
  have sThm : (14 : ℤ) ∣ a ↔ (7 : ℤ) ∣ a ∧ (2 : ℤ) ∣ a := by
    constructor
    · skip
      intro D1
      -- 1. obtain k: def:divides d := 14, n := a, from D1
      obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (14 : ℤ)) (n := a))).mp (by parley_side)
      -- 2. algebra, from 1
      have s2 : a = 7 * (2 * k) := by linear_combination s1
      -- 3. def:divides d := 7, n := a, from 2
      have s3 : (7 : ℤ) ∣ a := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (7 : ℤ)) (n := a))).mpr ⟨2 * k, by parley_side⟩
      -- 4. algebra, from 1
      have s4 : a = 2 * (7 * k) := by linear_combination s1
      -- 5. def:divides d := 2, n := a, from 4
      have s5 : (2 : ℤ) ∣ a := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := a))).mpr ⟨7 * k, by parley_side⟩
      -- 6. join 3, 5
      have s6 : (7 : ℤ) ∣ a ∧ (2 : ℤ) ∣ a := by parley_side
      all_goals parley_side
    · skip
      intro D2
      -- 7. obtain m: def:divides d := 7, n := a, from D2
      obtain ⟨m, s7⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (7 : ℤ)) (n := a))).mp (by parley_side)
      -- 8. obtain n: def:divides d := 2, n := a, from D2
      obtain ⟨n, s8⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := a))).mp (by parley_side)
      -- 9. algebra, from 7, 8
      have s9 : a = 14 * (n - 3 * m) := by linear_combination (-6) * s7 + (7) * s8
      -- 10. def:divides d := 14, n := a, from 9
      have s10 : (14 : ℤ) ∣ a := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (14 : ℤ)) (n := a))).mpr ⟨n - 3 * m, by parley_side⟩
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.FourteenDivides.FourteenDivides
