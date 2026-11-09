module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/rational-cube-root-of-two.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.RationalCubeRootOfTwo.OddCube

theorem odd_cube (n : ℤ) (hH2 : Odd n) :
    Odd (n ^ 3) := by
  -- 1. obtain k: def:odd, from H2
  obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := n))).mp hH2
  -- 2. substitute n = 2k + 1 (line 1)
  have s2 : n ^ 3 = (2 * k + 1) ^ 3 := by (have h := congrArg (fun t : ℤ => t ^ 3) s1; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 3. algebra
  have s3 : (2 * k + 1) ^ 3 = 2 * (4 * k ^ 3 + 6 * k ^ 2 + 3 * k) + 1 := by parley_ring
  -- 4. transitivity, from 2, 3
  have s4 : n ^ 3 = 2 * (4 * k ^ 3 + 6 * k ^ 2 + 3 * k) + 1 := by parley_side
  -- 5. def:odd n := n³, from 4
  exact ((Parley.Items.Stdlib.Divisibility.def_odd (n := n ^ 3))).mpr ⟨4 * k ^ 3 + 6 * k ^ 2 + 3 * k, s4⟩

end Parley.Proofs.Hammack.RationalCubeRootOfTwo.OddCube
