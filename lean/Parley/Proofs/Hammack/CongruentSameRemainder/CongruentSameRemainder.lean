module

public import NormTactics
public import Tactics
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/congruent-same-remainder.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CongruentSameRemainder.CongruentSameRemainder

theorem congruent_same_remainder (a : ℤ) (b : ℤ) (n : ℤ) (hH3 : 0 < n) (hH4 : a ≡ b [ZMOD n]) :
    a % n = b % n := by
  -- 1. def:congruent-mod, from H4
  have s1 : n ∣ a - b := by exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := a) (b := b))).mp hH4
  -- 2. obtain k: def:divides d := n, n := a − b, from 1
  obtain ⟨k, s2⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := n) (n := a - b))).mp s1
  -- 3. mun:mod-multiple r := b, m := n, q := k
  have s3 : (k * n + b) % n = b % n := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := b) (m := n) hH3 (q := k))
  -- 4. substitute
  have c1 : k * n + b = a := by linear_combination (norm := parley_norm) (-1) * s2
  have row1 : a % n = b % n := by (have h := Eq.subst (motive := (fun t : ℤ => t % n = b % n)) c1 s3; push_cast at h ⊢; all_goals exact_mod_cast h)
  exact row1

end Parley.Proofs.Hammack.CongruentSameRemainder.CongruentSameRemainder
