module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/negative-of-rational.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.NegativeOfRational.NegativeOfRational

theorem negative_of_rational (A : ℚ) :
    True := by
  -- 1. obtain p, q: def:rational x := A
  obtain ⟨p, q, s1a, s1b⟩ := ((Parley.Items.Stdlib.Numbers.def_rational (x := A))).mp ⟨_, rfl⟩
  -- 2. calculation
  have s2 : -A = -(p : ℚ) / (q : ℚ) := by
    calc -A = -((p : ℚ) / (q : ℚ)) := by (have h := congrArg (fun t : ℚ => -t) s1b; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = -(p : ℚ) / (q : ℚ) := by parley_ring
  -- 3. def:rational x := −A, from 2
  exact trivial

end Parley.Proofs.Setmm.NegativeOfRational.NegativeOfRational
