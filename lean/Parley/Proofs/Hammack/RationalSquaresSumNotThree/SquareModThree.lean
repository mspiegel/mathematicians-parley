module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Reasoning
public import Parley.Proofs.Hammack.CubeCongruentModThree.ResidueModThree

/-! Written from proofs/hammack/rational-squares-sum-not-three.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.RationalSquaresSumNotThree.SquareModThree

theorem square_mod_three (n : ℤ) :
    ((3 : ℤ) ∣ n ^ 2 ∨ (3 : ℤ) ∣ n ^ 2 - 1) := by
  -- 1. mun:mod-less a := n, b := 3
  have s1 : n % (3 : ℤ) < 3 := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := n) (b := (3 : ℤ)) (by norm_num))
  -- 2. thm:residue-mod-three r := n mod 3, from 1
  have s2 : (n % (3 : ℤ) = 0 ∨ n % (3 : ℤ) = 1) ∨ n % (3 : ℤ) = 2 := by exact (Parley.Proofs.Hammack.CubeCongruentModThree.ResidueModThree.residue_mod_three (r := n % (3 : ℤ)) (Int.emod_nonneg _ (ne_of_gt (by norm_num))) s1)
  -- 3. obtain q: mun:mod-remainder a := n, m := 3, r := n mod 3, from 1
  obtain ⟨q, s3⟩ := ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := n) (m := (3 : ℤ)) (by norm_num) (r := n % (3 : ℤ)) (Int.emod_nonneg _ (ne_of_gt (by norm_num))) s1)).mp rfl
  -- 4. cases, from 2
  rcases s2 with (hC1 | hC2) | hC3
  · skip
    -- 4.1. substitute n mod 3 = 0 (C1) into line 3
    have s4_1 : q * 3 = n := by (have h := Eq.subst (motive := (fun t : ℤ => q * 3 + t = n)) hC1 s3; push_cast [add_zero] at h ⊢; exact_mod_cast h)
    -- 4.2. algebra, from 4.1
    have s4_2 : n ^ 2 = 3 * (3 * q ^ 2) := by linear_combination (-n - 3 * q) * s4_1
    -- 4.3. def:divides d := 3, n := n², from 4.2
    have s4_3 : (3 : ℤ) ∣ n ^ 2 := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := n ^ 2))).mpr ⟨3 * q ^ 2, s4_2⟩
    -- 4.4. mun:or-left, from 4.3
    exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := (3 : ℤ) ∣ n ^ 2) (Q := (3 : ℤ) ∣ n ^ 2 - 1) s4_3)
  · skip
    -- 4.5. substitute n mod 3 = 1 (C2) into line 3
    have s4_5 : q * 3 + 1 = n := Eq.subst (motive := (fun t : ℤ => q * 3 + t = n)) hC2 s3
    -- 4.6. algebra, from 4.5
    have s4_6 : n ^ 2 - 1 = 3 * (3 * q ^ 2 + 2 * q) := by linear_combination (-n - 3 * q - 1) * s4_5
    -- 4.7. def:divides d := 3, n := n² − 1, from 4.6
    have s4_7 : (3 : ℤ) ∣ n ^ 2 - 1 := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := n ^ 2 - 1))).mpr ⟨3 * q ^ 2 + 2 * q, s4_6⟩
    -- 4.8. mun:or-right, from 4.7
    exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (3 : ℤ) ∣ n ^ 2) (Q := (3 : ℤ) ∣ n ^ 2 - 1) s4_7)
  · skip
    -- 4.9. substitute n mod 3 = 2 (C3) into line 3
    have s4_9 : q * 3 + 2 = n := Eq.subst (motive := (fun t : ℤ => q * 3 + t = n)) hC3 s3
    -- 4.10. algebra, from 4.9
    have s4_10 : n ^ 2 - 1 = 3 * (3 * q ^ 2 + 4 * q + 1) := by linear_combination (-n - 3 * q - 2) * s4_9
    -- 4.11. def:divides d := 3, n := n² − 1, from 4.10
    have s4_11 : (3 : ℤ) ∣ n ^ 2 - 1 := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := n ^ 2 - 1))).mpr ⟨3 * q ^ 2 + 4 * q + 1, s4_10⟩
    -- 4.12. mun:or-right, from 4.11
    exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (3 : ℤ) ∣ n ^ 2) (Q := (3 : ℤ) ∣ n ^ 2 - 1) s4_11)

end Parley.Proofs.Hammack.RationalSquaresSumNotThree.SquareModThree
