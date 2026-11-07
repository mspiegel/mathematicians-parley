module

public import ArithTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/a-there-is-unfolded-where-the-scope-binds-its-letter.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AThereIsUnfoldedWhereTheScopeBindsItsLetter.AThereIsUnfoldedWhereTheScopeBindsItsLetter

theorem a_there_is_unfolded_where_the_scope_binds_its_letter (p : ℤ) (hH2 : (3 : ℤ) ∣ p) :
    ¬ ¬ (∃ s : ℤ, p = 3 * s) := by
  -- 1. contradiction
  have s1 : ¬ ¬ (∃ s : ℤ, p = 3 * s) := by
    by_contra hc_hS
    have hS : ¬ (∃ s : ℤ, p = 3 * s) := by parley_suppose hc_hS
    -- 1.1. def:divides d := 3, n := p, from H2
    have s1_1 : ∃ s : ℤ, p = 3 * s := by first | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := p))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := p))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := p))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := p))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := p))).mp (by parley_side); parley_side)
    all_goals parley_side
  all_goals exact s1

end Parley.Tests.Elaborator.AThereIsUnfoldedWhereTheScopeBindsItsLetter.AThereIsUnfoldedWhereTheScopeBindsItsLetter
