module

public import NormTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Reasoning
public import Parley.Proofs.Hammack.CubeCongruentModThree.ResidueModThree

/-! Written from proofs/hammack/rational-squares-sum-not-three.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.RationalSquaresSumNotThree.SquareModThree

set_option maxHeartbeats 400000 in
theorem square_mod_three (n : ℤ) :
    ((3 : ℤ) ∣ n ^ 2 ∨ (3 : ℤ) ∣ n ^ 2 - 1) := by
  -- 1. mun:mod-natural a := n, b := 3
  have s1 : 0 ≤ n % (3 : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := n) (b := (3 : ℤ)) (by parley_side))
  -- 2. mun:mod-less a := n, b := 3
  have s2 : n % (3 : ℤ) < 3 := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := n) (b := (3 : ℤ)) (by parley_side))
  -- 3. thm:residue-mod-three r := n mod 3, from 1, 2
  have s3 : (n % (3 : ℤ) = 0 ∨ n % (3 : ℤ) = 1) ∨ n % (3 : ℤ) = 2 := by exact (Parley.Proofs.Hammack.CubeCongruentModThree.ResidueModThree.residue_mod_three (r := n % (3 : ℤ)) (by parley_side) s2)
  -- 4. obtain q: mun:mod-remainder a := n, m := 3, r := n mod 3, from 1, 2
  obtain ⟨q, s4⟩ := ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := n) (m := (3 : ℤ)) (by parley_side) (r := n % (3 : ℤ)) (by parley_side) s2)).mp (by parley_side)
  -- 5. cases, from 3
  rcases s3 with (hC1 | hC2) | hC3
  · skip
    -- 5.1. substitute n mod 3 = 0 (C1) into line 4
    have s5_1 : q * 3 = n := by parley_subst_at hC1 s4
    -- 5.2. algebra, from 5.1
    have s5_2 : n ^ 2 = 3 * (3 * q ^ 2) := by linear_combination (norm := parley_norm) (-n - 3 * q) * s5_1
    -- 5.3. def:divides d := 3, n := n², from 5.2
    have s5_3 : (3 : ℤ) ∣ n ^ 2 := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := n ^ 2))).mpr ⟨3 * q ^ 2, s5_2⟩
    -- 5.4. mun:or-left, from 5.3
    exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := (3 : ℤ) ∣ n ^ 2) (Q := (3 : ℤ) ∣ n ^ 2 - 1) s5_3)
  · skip
    -- 5.5. substitute n mod 3 = 1 (C2) into line 4
    have s5_5 : q * 3 + 1 = n := by parley_subst_at hC2 s4
    -- 5.6. algebra, from 5.5
    have s5_6 : n ^ 2 - 1 = 3 * (3 * q ^ 2 + 2 * q) := by linear_combination (norm := parley_norm) (-n - 3 * q - 1) * s5_5
    -- 5.7. def:divides d := 3, n := n² − 1, from 5.6
    have s5_7 : (3 : ℤ) ∣ n ^ 2 - 1 := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := n ^ 2 - 1))).mpr ⟨3 * q ^ 2 + 2 * q, s5_6⟩
    -- 5.8. mun:or-right, from 5.7
    exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (3 : ℤ) ∣ n ^ 2) (Q := (3 : ℤ) ∣ n ^ 2 - 1) s5_7)
  · skip
    -- 5.9. substitute n mod 3 = 2 (C3) into line 4
    have s5_9 : q * 3 + 2 = n := by parley_subst_at hC3 s4
    -- 5.10. algebra, from 5.9
    have s5_10 : n ^ 2 - 1 = 3 * (3 * q ^ 2 + 4 * q + 1) := by linear_combination (norm := parley_norm) (-n - 3 * q - 2) * s5_9
    -- 5.11. def:divides d := 3, n := n² − 1, from 5.10
    have s5_11 : (3 : ℤ) ∣ n ^ 2 - 1 := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := n ^ 2 - 1))).mpr ⟨3 * q ^ 2 + 4 * q + 1, s5_10⟩
    -- 5.12. mun:or-right, from 5.11
    exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (3 : ℤ) ∣ n ^ 2) (Q := (3 : ℤ) ∣ n ^ 2 - 1) s5_11)

end Parley.Proofs.Hammack.RationalSquaresSumNotThree.SquareModThree
