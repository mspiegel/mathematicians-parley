module

public import AlgebraTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/rational-closure.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.RationalClosure.RationalNegative

theorem rational_negative (A : ℚ) :
    True := by
  -- 1. obtain p, q: def:rational x := A
  obtain ⟨p, q, s1a, s1b⟩ := ((Parley.Items.Stdlib.Numbers.def_rational (x := A))).mp (by parley_side)
  try lift q to ℕ using le_of_lt s1a
  -- 2. algebra, from 1
  have s2 : -A = -(p : ℚ) / (q : ℚ) := by linear_combination (norm := parley_field) (-1) * s1b
  -- 3. exhibit, from 2
  have s3 : ∃ a : ℤ, ∃ b : ℕ, 0 < b ∧ -A = (a : ℚ) / (b : ℚ) := ⟨-p, q, by parley_side, by parley_side⟩
  -- 4. def:rational x := −A, from 3
  all_goals parley_side

end Parley.Proofs.Setmm.RationalClosure.RationalNegative
