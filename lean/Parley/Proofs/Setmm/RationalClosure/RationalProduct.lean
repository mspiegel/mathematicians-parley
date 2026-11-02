module

public import LeanBridges
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/rational-closure.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.RationalClosure.RationalProduct

theorem rational_product (A : ℚ) (B : ℚ) :
    True := by
  -- 1. obtain p, q: def:rational x := A
  obtain ⟨p, q, s1a, s1b⟩ := ((Parley.Items.Stdlib.Numbers.def_rational (x := A))).mp (by parley_side)
  -- 2. obtain r, s: def:rational x := B
  obtain ⟨r, s, s2a, s2b⟩ := ((Parley.Items.Stdlib.Numbers.def_rational (x := B))).mp (by parley_side)
  -- 3. calculation
  have s3 : A * B = (p : ℚ) * (r : ℚ) / ((q : ℚ) * (s : ℚ)) := by
    calc A * B = (p : ℚ) / (q : ℚ) * B := by parley_subst s1b
      _ = (p : ℚ) / (q : ℚ) * ((r : ℚ) / (s : ℚ)) := by parley_subst s2b
      _ = (p : ℚ) * (r : ℚ) / ((q : ℚ) * (s : ℚ)) := by parley_ring
  -- 4. exhibit, from 3
  have s4 : ∃ a : ℤ, ∃ b : ℕ, 0 < b ∧ A * B = (a : ℚ) / (b : ℚ) := ⟨p * r, q * s, by parley_side, by parley_side⟩
  -- 5. def:rational x := A·B, from 4
  all_goals parley_side

end Parley.Proofs.Setmm.RationalClosure.RationalProduct
