module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/rational-times-denominator.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.RationalTimesDenominator.RationalTimesDenominator

theorem rational_times_denominator (A : ℚ) :
    (∃ x : ℕ, 0 < x ∧ (∃ m : ℤ, (m : ℚ) = A * (x : ℚ))) := by
  -- 1. obtain p, q: def:rational x := A
  obtain ⟨p, q, s1a, s1b⟩ := ((Parley.Items.Stdlib.Numbers.def_rational (x := A))).mp (by parley_side)
  -- 2. algebra, from 1
  have s2 : A * (q : ℚ) = (p : ℚ) := by linear_combination (norm := parley_field) ((q : ℚ)) * s1b
  -- 3. membership, from 2
  have s3 : ∃ m : ℤ, (m : ℚ) = A * (q : ℚ) := ⟨p, by first | (push_cast; linarith [s2]) | (rw [s2]; push_cast; ring) | (rw [← s2]; push_cast; ring) | exact s2 | exact s2.symm⟩
  -- 4. exhibit, from 3
  have s4 : ∃ x : ℕ, 0 < x ∧ (∃ m : ℤ, (m : ℚ) = A * (x : ℚ)) := ⟨q, by parley_side, by parley_side⟩
  all_goals parley_side

end Parley.Proofs.Setmm.RationalTimesDenominator.RationalTimesDenominator
