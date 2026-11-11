module

public import AlgebraTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/substitute-rows.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.SubstituteRows.SubstituteRows

theorem substitute_rows (n : ℤ) (d : ℤ) (hH3 : d ∣ n + 1) (hH4 : d ∣ n) :
    d ∣ (1 : ℤ) := by
  -- 1. mun:divides-difference a := n + 1, b := n, from H3, H4
  have s1 : d ∣ n + 1 - n := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := d) (a := n + 1) (b := n) hH3 hH4)
  -- 2. substitute
  have c1 : n + 1 - n = 1 := by parley_ring
  have row1 : d ∣ (1 : ℤ) := by (have h := Eq.subst (motive := (fun t : ℤ => d ∣ t)) c1 s1; push_cast at h ⊢; all_goals exact_mod_cast h)
  exact row1

end Parley.Tests.Elaborator.SubstituteRows.SubstituteRows
