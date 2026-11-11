module

public import AlgebraTactics
public import ArithTactics
public import NormTactics
public import Tactics
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Parley.Items.Stdlib.Divisibility
public import Parley.Proofs.Hammack.RationalCubeRootOfTwo.EvenCube
public import Parley.Proofs.Wiedijk.Sqrt2Irrational.LowestTerms

/-! Written from proofs/hammack/rational-cube-root-of-two.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.RationalCubeRootOfTwo.RationalCubeRootOfTwo

theorem rational_cube_root_of_two :
    ¬ (∃ x : ℚ, x ^ 3 = 2) := by
  -- the theorem. contradiction
  intro hS
  -- 1. obtain x from S
  obtain ⟨x, s1⟩ := hS
  -- 2. obtain p, q: thm:lowest-terms
  obtain ⟨p, q, ⟨⟨s2a, s2b⟩, s2c⟩⟩ := (Parley.Proofs.Wiedijk.Sqrt2Irrational.LowestTerms.lowest_terms (x := x))
  -- 3. substitute x = p/q (line 2) into line 1
  have s3 : ((p : ℚ) / (q : ℚ)) ^ 3 = 2 := by (have h := Eq.subst (motive := (fun t : ℚ => t ^ 3 = 2)) s2b s1; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 4. algebra, from 3
  have r75_1 : q ≠ 0 := by parley_side
  have s4 : p ^ 3 = 2 * q ^ 3 := by qify at *; linear_combination (norm := parley_field) ((q : ℚ) ^ 3) * s3
  -- 5. def:even n := p³, from 4
  have s5 : Even (p ^ 3) := ((Parley.Items.Stdlib.Divisibility.def_even (n := p ^ 3))).mpr ⟨q ^ 3, s4⟩
  -- 6. thm:even-cube n := p, from 5
  have s6 : Even p := by exact (Parley.Proofs.Hammack.RationalCubeRootOfTwo.EvenCube.even_cube (n := p) (by parley_side))
  -- 7. obtain r: def:even n := p, from 6
  obtain ⟨r, s7⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := p))).mp s6
  -- 8. substitute p = 2r (line 7) into line 4
  have s8 : (2 * r) ^ 3 = 2 * q ^ 3 := by (have h := Eq.subst (motive := (fun t : ℤ => t ^ 3 = 2 * q ^ 3)) s7 s4; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 9. algebra, from 8
  have s9 : q ^ 3 = 2 * (2 * r ^ 3) := by qify at *; linear_combination (norm := parley_norm) (-(1 / 2 : ℚ)) * s8
  -- 10. def:even n := q³, from 9
  have s10 : Even (q ^ 3) := ((Parley.Items.Stdlib.Divisibility.def_even (n := q ^ 3))).mpr ⟨2 * r ^ 3, s9⟩
  -- 11. thm:even-cube n := q, from 10
  have s11 : Even q := by exact (Parley.Proofs.Hammack.RationalCubeRootOfTwo.EvenCube.even_cube (n := q) (by parley_side))
  -- 12. obtain s: def:even n := q, from 11
  obtain ⟨s, s12⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := q))).mp s11
  -- 13. def:divides d := 2, n := p, from 7
  have s13 : (2 : ℤ) ∣ p := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := p))).mpr ⟨r, s7⟩
  -- 14. def:divides d := 2, n := q, from 12
  have s14 : (2 : ℤ) ∣ q := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := q))).mpr ⟨s, s12⟩
  -- 15. exhibit, from 13, 14
  have r109_1 : (2 : ℤ) > 1 := by parley_arith
  have s15 : ∃ d : ℤ, (d > 1 ∧ d ∣ p) ∧ d ∣ q := ⟨(2 : ℤ), ⟨⟨r109_1, s13⟩, s14⟩⟩
  exact s2c s15

end Parley.Proofs.Hammack.RationalCubeRootOfTwo.RationalCubeRootOfTwo
