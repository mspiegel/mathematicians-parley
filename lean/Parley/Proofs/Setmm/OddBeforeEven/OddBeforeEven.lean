module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Library

/-! Written from proofs/setmm/odd-before-even.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.OddBeforeEven.OddBeforeEven

theorem odd_before_even (N : ℤ) :
    (Odd N ↔ (2 : ℤ) ∣ N + 1) := by
  -- the theorem. both directions
  have sThm : Odd N ↔ (2 : ℤ) ∣ N + 1 := by
    constructor
    · skip
      intro hD1
      -- 1. obtain k: def:odd, from D1
      obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := N))).mp (by parley_side)
      -- 2. algebra, from 1
      have s2 : N + 1 = 2 * (k + 1) := by linear_combination s1
      -- 3. def:divides d := 2, n := N + 1, from 2
      have s3 : (2 : ℤ) ∣ N + 1 := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := N + 1))).mpr ⟨k + 1, by parley_side⟩
      all_goals parley_side
    · skip
      intro hD2
      -- 4. obtain j: def:divides d := 2, n := N + 1, from D2
      obtain ⟨j, s4⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := N + 1))).mp (by parley_side)
      -- 5. algebra, from 4
      have s5 : N = 2 * (j - 1) + 1 := by linear_combination s4
      -- 6. def:odd n := N, from 5
      have s6 : Odd N := ((Parley.Items.Stdlib.Divisibility.def_odd (n := N))).mpr ⟨j - 1, by parley_side⟩
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.OddBeforeEven.OddBeforeEven
