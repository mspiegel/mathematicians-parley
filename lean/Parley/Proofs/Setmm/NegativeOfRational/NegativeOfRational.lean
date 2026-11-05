module

public import AlgebraTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/negative-of-rational.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.NegativeOfRational.NegativeOfRational

theorem negative_of_rational (A : ℚ) :
    True := by
  -- 1. obtain p, q: def:rational x := A
  obtain ⟨p, q, s1a, s1b⟩ := ((Parley.Items.Stdlib.Numbers.def_rational (x := A))).mp (by parley_side)
  try lift q to ℕ using le_of_lt s1a
  -- 2. calculation
  have s2 : -A = -(p : ℚ) / (q : ℚ) := by
    calc -A = -((p : ℚ) / (q : ℚ)) := by parley_subst s1b
      _ = -(p : ℚ) / (q : ℚ) := by parley_ring
  -- 3. def:rational x := −A, from 2
  all_goals parley_side

end Parley.Proofs.Setmm.NegativeOfRational.NegativeOfRational
