module

public import AlgebraTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/rational-closure.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.RationalClosure.RationalSum

theorem rational_sum (A : ℚ) (B : ℚ) :
    True := by
  -- 1. obtain p, q: def:rational x := A
  obtain ⟨p, q, s1a, s1b⟩ := ((Parley.Items.Stdlib.Numbers.def_rational (x := A))).mp (by parley_side)
  -- 2. obtain r, s: def:rational x := B
  obtain ⟨r, s, s2a, s2b⟩ := ((Parley.Items.Stdlib.Numbers.def_rational (x := B))).mp (by parley_side)
  -- 3. algebra, from 1, 2
  have s3 : A + B = ((p : ℚ) * (s : ℚ) + (r : ℚ) * (q : ℚ)) / ((q : ℚ) * (s : ℚ)) := by linear_combination (norm := parley_field) s1b + s2b
  -- 4. exhibit, from 3
  have s4 : ∃ a : ℤ, ∃ b : ℕ, 0 < b ∧ A + B = (a : ℚ) / (b : ℚ) := ⟨p * (s : ℤ) + r * (q : ℤ), q * s, by parley_side, by parley_side⟩
  -- 5. def:rational x := A + B, from 4
  all_goals parley_side

end Parley.Proofs.Setmm.RationalClosure.RationalSum
