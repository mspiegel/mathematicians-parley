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
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Proofs.Hammack.CubeCongruentModThree.ResidueModThree

/-! Written from proofs/hammack/cube-congruent-mod-three.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CubeCongruentModThree.CubeCongruentModThree

theorem cube_congruent_mod_three (a : ℤ) :
    a ^ 3 ≡ a [ZMOD (3 : ℤ)] := by
  -- 1. mun:mod-less b := 3
  have s1 : a % (3 : ℤ) < 3 := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := a) (b := (3 : ℤ)) (by norm_num))
  -- 2. thm:residue-mod-three r := a mod 3, from 1
  have s2 : (a % (3 : ℤ) = 0 ∨ a % (3 : ℤ) = 1) ∨ a % (3 : ℤ) = 2 := by exact (Parley.Proofs.Hammack.CubeCongruentModThree.ResidueModThree.residue_mod_three (r := a % (3 : ℤ)) (Int.emod_nonneg _ (ne_of_gt (by norm_num))) s1)
  -- 3. obtain q: mun:mod-remainder m := 3, r := a mod 3, from 1
  obtain ⟨q, s3⟩ := ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := a) (m := (3 : ℤ)) (by norm_num) (r := a % (3 : ℤ)) (Int.emod_nonneg _ (ne_of_gt (by norm_num))) s1)).mp rfl
  -- 4. cases, from 2
  have s4 : (3 : ℤ) ∣ a ^ 3 - a := by
    rcases s2 with (hC1 | hC2) | hC3
    · skip
      -- 4.1. substitute a mod 3 = 0 (C1) into line 3
      have s4_1 : q * 3 = a := by (have h := Eq.subst (motive := (fun t : ℤ => q * 3 + t = a)) hC1 s3; push_cast [add_zero] at h ⊢; exact_mod_cast h)
      -- 4.2. calculation
      have s4_2 : a ^ 3 - a = 3 * (9 * q ^ 3 - q) := by
        calc a ^ 3 - a = (q * 3) ^ 3 - q * 3 := congrArg (fun t : ℤ => t ^ 3 - t) s4_1.symm
          _ = 3 * (9 * q ^ 3 - q) := by ring1
      -- 4.3. def:divides d := 3, n := a³ − a, from 4.2
      exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := a ^ 3 - a))).mpr ⟨9 * q ^ 3 - q, s4_2⟩
    · skip
      -- 4.4. substitute a mod 3 = 1 (C2) into line 3
      have s4_4 : q * 3 + 1 = a := Eq.subst (motive := (fun t : ℤ => q * 3 + t = a)) hC2 s3
      -- 4.5. calculation
      have s4_5 : a ^ 3 - a = 3 * (9 * q ^ 3 + 9 * q ^ 2 + 2 * q) := by
        calc a ^ 3 - a = (q * 3 + 1) ^ 3 - (q * 3 + 1) := congrArg (fun t : ℤ => t ^ 3 - t) s4_4.symm
          _ = 3 * (9 * q ^ 3 + 9 * q ^ 2 + 2 * q) := by ring1
      -- 4.6. def:divides d := 3, n := a³ − a, from 4.5
      exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := a ^ 3 - a))).mpr ⟨9 * q ^ 3 + 9 * q ^ 2 + 2 * q, s4_5⟩
    · skip
      -- 4.7. substitute a mod 3 = 2 (C3) into line 3
      have s4_7 : q * 3 + 2 = a := Eq.subst (motive := (fun t : ℤ => q * 3 + t = a)) hC3 s3
      -- 4.8. calculation
      have s4_8 : a ^ 3 - a = 3 * (9 * q ^ 3 + 18 * q ^ 2 + 11 * q + 2) := by
        calc a ^ 3 - a = (q * 3 + 2) ^ 3 - (q * 3 + 2) := congrArg (fun t : ℤ => t ^ 3 - t) s4_7.symm
          _ = 3 * (9 * q ^ 3 + 18 * q ^ 2 + 11 * q + 2) := by ring1
      -- 4.9. def:divides d := 3, n := a³ − a, from 4.8
      exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := a ^ 3 - a))).mpr ⟨9 * q ^ 3 + 18 * q ^ 2 + 11 * q + 2, s4_8⟩
  -- 5. def:congruent-mod, from 4
  exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (3 : ℤ)) (a := a ^ 3) (b := a))).mpr s4

end Parley.Proofs.Hammack.CubeCongruentModThree.CubeCongruentModThree
