module

public import NormTactics
public import Tactics
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Proofs.Hammack.GcdWithRemainder.GcdWithRemainder

/-! Written from proofs/hammack/congruent-same-gcd.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CongruentSameGcd.CongruentSameGcd

theorem congruent_same_gcd (a : ℤ) (b : ℤ) (n : ℤ) (hH3 : 0 < n) (hH4 : a ≡ b [ZMOD n]) :
    (Int.gcd a n : ℤ) = (Int.gcd b n : ℤ) := by
  -- 1. def:congruent-mod, from H4
  have s1 : n ∣ a - b := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := a) (b := b))).mp hH4
  -- 2. obtain k: def:divides d := n, n := a − b, from 1
  obtain ⟨k, s2⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := n) (n := a - b))).mp s1
  -- 3. algebra, from 2
  have s3 : a = k * n + b := by linear_combination (norm := parley_norm) s2
  -- 4. thm:gcd-with-remainder b := n, q := k, r := b, from 3
  exact (Parley.Proofs.Hammack.GcdWithRemainder.GcdWithRemainder.gcd_with_remainder (a := a) (b := n) (by parley_side) (q := k) (r := b) s3)

end Parley.Proofs.Hammack.CongruentSameGcd.CongruentSameGcd
