module

public import Mathlib.Tactic.NormNum
public import Lean.Elab.MutualDef
public import Lean.Parser.Command
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# Factorials and binomial coefficients as the page reads them

The page writes n! and C(n, k) of integers: (n − k)! inside the formula for
C(n, k), and C(n, k − 1) in Pascal's rule. Mathlib's `Nat.factorial` and
`Nat.choose` take naturals, and a natural subtraction stops at 0, so each is
taken here of integers and is Mathlib's on the naturals.

- n! is `Nat.factorial` of n's `toNat`. The page writes it only where n is
  not negative.
- C(n, k) is set.mm's: `Nat.choose` where k is not negative, which is
  already 0 above n, and 0 where k is negative.

The definitions stand apart from the theorems about them (`Counting`), so
that the tactics, which unfold them, rebuild only when they change.
-/

public section

namespace LeanBridges.Counting

/-- n! of an integer n that is not negative: `Nat.factorial n.toNat`. -/
@[expose] def factorial (n : ℤ) : ℕ :=
  n.toNat.factorial

/-- C(n, k): `Nat.choose n k` for k ≥ 0, and 0 for k < 0. -/
@[expose] def choose (n k : ℤ) : ℕ :=
  if 0 ≤ k then Nat.choose n.toNat k.toNat else 0

/-- A natural's factorial is Mathlib's. -/
@[simp] theorem factorial_natCast (n : ℕ) : factorial n = n.factorial := by
  simp [factorial]

/-- A numeral's factorial is Mathlib's, so that `norm_num` works it out. -/
@[simp] theorem factorial_ofNat (n : ℕ) [n.AtLeastTwo] :
    factorial (no_index (OfNat.ofNat n : ℤ)) = (OfNat.ofNat n : ℕ).factorial := rfl

@[simp] theorem factorial_zero : factorial 0 = 1 := rfl

@[simp] theorem factorial_one : factorial 1 = 1 := rfl

/-- A coefficient of naturals is Mathlib's. -/
@[simp] theorem choose_natCast (n k : ℕ) : choose n k = n.choose k := by
  simp [choose]

end LeanBridges.Counting
