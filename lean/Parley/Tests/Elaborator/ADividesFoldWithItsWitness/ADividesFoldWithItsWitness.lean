module

public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/a-divides-fold-with-its-witness.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ADividesFoldWithItsWitness.ADividesFoldWithItsWitness

theorem a_divides_fold_with_its_witness (m : ℤ) (hH2 : 0 < m) (hH3 : ∃ j : ℤ, ∃ k : ℤ, j ^ 2 + k ^ 2 = 3 * m ^ 2) :
    (3 : ℤ) ∣ 3 * m ^ 2 := by
  -- 1. obtain p, q from H3
  obtain ⟨p, q, s1⟩ := hH3
  -- 2. def:divides d := 3, n := p² + q², from H2, 1
  have s2 : (3 : ℤ) ∣ p ^ 2 + q ^ 2 := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := p ^ 2 + q ^ 2))).mpr ⟨m ^ 2, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := p ^ 2 + q ^ 2))).mpr ⟨m ^ 2, by parley_side⟩; parley_side)
  -- 3. substitute p² + q² = 3m² (line 1) into line 2
  have s3 : (3 : ℤ) ∣ 3 * m ^ 2 := by parley_subst_at s1 s2
  all_goals exact s3

end Parley.Tests.Elaborator.ADividesFoldWithItsWitness.ADividesFoldWithItsWitness
