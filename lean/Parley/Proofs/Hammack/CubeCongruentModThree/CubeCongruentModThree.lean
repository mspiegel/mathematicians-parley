module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Proofs.Hammack.CubeCongruentModThree.ResidueModThree

/-! Written from proofs/hammack/cube-congruent-mod-three.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CubeCongruentModThree.CubeCongruentModThree

theorem cube_congruent_mod_three (a : ℤ) :
    a ^ 3 ≡ a [ZMOD (3 : ℤ)] := by
  -- 1. mun:mod-natural b := 3
  have s1 : 0 ≤ a % (3 : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := a) (b := (3 : ℤ)) (by parley_side))
  -- 2. mun:mod-less b := 3
  have s2 : a % (3 : ℤ) < 3 := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := a) (b := (3 : ℤ)) (by parley_side))
  -- 3. thm:residue-mod-three r := a mod 3, from 1, 2
  have s3 : (a % (3 : ℤ) = 0 ∨ a % (3 : ℤ) = 1) ∨ a % (3 : ℤ) = 2 := by exact (Parley.Proofs.Hammack.CubeCongruentModThree.ResidueModThree.residue_mod_three (r := a % (3 : ℤ)) s1 s2)
  -- 4. obtain q: mun:mod-remainder m := 3, r := a mod 3, from 1, 2
  obtain ⟨q, s4⟩ := ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := a) (m := (3 : ℤ)) (by parley_side) (r := a % (3 : ℤ)) s1 s2)).mp (by parley_side)
  -- 5. cases, from 3
  have s5 : (3 : ℤ) ∣ a ^ 3 - a := by
    rcases s3 with (hC1 | hC2) | hC3
    · skip
      -- 5.1. substitute a mod 3 = 0 (C1) into line 4
      have s5_1 : q * 3 = a := by (have h := Eq.subst (motive := (fun t : ℤ => q * 3 + t = a)) hC1 s4; push_cast [add_zero] at h ⊢; all_goals exact_mod_cast h)
      -- 5.2. calculation
      have s5_2 : a ^ 3 - a = 3 * (9 * q ^ 3 - q) := by
        calc a ^ 3 - a = (q * 3) ^ 3 - q * 3 := by (have h := congrArg (fun t : ℤ => t ^ 3 - t) s5_1.symm; push_cast at h ⊢; all_goals exact_mod_cast h)
          _ = 3 * (9 * q ^ 3 - q) := by parley_ring
      -- 5.3. def:divides d := 3, n := a³ − a, from 5.2
      exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := a ^ 3 - a))).mpr ⟨9 * q ^ 3 - q, s5_2⟩
    · skip
      -- 5.4. substitute a mod 3 = 1 (C2) into line 4
      have s5_4 : q * 3 + 1 = a := by (have h := Eq.subst (motive := (fun t : ℤ => q * 3 + t = a)) hC2 s4; push_cast at h ⊢; all_goals exact_mod_cast h)
      -- 5.5. calculation
      have s5_5 : a ^ 3 - a = 3 * (9 * q ^ 3 + 9 * q ^ 2 + 2 * q) := by
        calc a ^ 3 - a = (q * 3 + 1) ^ 3 - (q * 3 + 1) := by (have h := congrArg (fun t : ℤ => t ^ 3 - t) s5_4.symm; push_cast at h ⊢; all_goals exact_mod_cast h)
          _ = 3 * (9 * q ^ 3 + 9 * q ^ 2 + 2 * q) := by parley_ring
      -- 5.6. def:divides d := 3, n := a³ − a, from 5.5
      exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := a ^ 3 - a))).mpr ⟨9 * q ^ 3 + 9 * q ^ 2 + 2 * q, s5_5⟩
    · skip
      -- 5.7. substitute a mod 3 = 2 (C3) into line 4
      have s5_7 : q * 3 + 2 = a := by (have h := Eq.subst (motive := (fun t : ℤ => q * 3 + t = a)) hC3 s4; push_cast at h ⊢; all_goals exact_mod_cast h)
      -- 5.8. calculation
      have s5_8 : a ^ 3 - a = 3 * (9 * q ^ 3 + 18 * q ^ 2 + 11 * q + 2) := by
        calc a ^ 3 - a = (q * 3 + 2) ^ 3 - (q * 3 + 2) := by (have h := congrArg (fun t : ℤ => t ^ 3 - t) s5_7.symm; push_cast at h ⊢; all_goals exact_mod_cast h)
          _ = 3 * (9 * q ^ 3 + 18 * q ^ 2 + 11 * q + 2) := by parley_ring
      -- 5.9. def:divides d := 3, n := a³ − a, from 5.8
      exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := a ^ 3 - a))).mpr ⟨9 * q ^ 3 + 18 * q ^ 2 + 11 * q + 2, s5_8⟩
  -- 6. def:congruent-mod, from 5
  exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (3 : ℤ)) (a := a ^ 3) (b := a))).mpr s5

end Parley.Proofs.Hammack.CubeCongruentModThree.CubeCongruentModThree
