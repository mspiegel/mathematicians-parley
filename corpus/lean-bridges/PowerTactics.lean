module

public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination
public import Lean.Parser.Command
public import Mathlib.Algebra.Field.Defs
public import Tactics
public import NormTactics

/-!
# Natural numbers given as an integer's `toNat`

Where the page's natural number is an integer a line shows not negative,
the build writes its `toNat`: `parley_cast_toNat` casts it back, and
`parley_zpow_toNat` takes an integer power to the natural power at a step
that names the exponent's fact. A generated file imports this module only
when it names one of them.
-/

public section

/-- An integer power to an exponent at least 0 is the natural power to its
`toNat`: a line of a field, (−1)^n in ℚ, said where the claim is of
integers, (−1)^(n.toNat) in ℤ, which has no integer powers. -/
theorem parley_zpow_toNat {K : Type*} [DivisionRing K] (a : K) (n : ℤ) (h : 0 ≤ n) :
    a ^ n = a ^ n.toNat := by
  rw [← zpow_natCast, Int.toNat_of_nonneg h]

/-- An integer not negative, cast to any ring from the natural number its
`toNat` is, is itself: the build gives a natural letter an integer the page
shows is not negative as its `toNat` (`theorem::witness`). -/
theorem parley_cast_toNat {R : Type*} [Ring R] {n : ℤ} (h : 0 ≤ n) :
    ((n.toNat : ℕ) : R) = (n : R) := by
  rw [← Int.cast_natCast, Int.toNat_of_nonneg h]

/-- A line that says something of a whole number a term is, `∃ m : ℤ, (m :
ℚ) = 2 ^ (p − 1) ∧ 2 ^ p − 1 ∣ m`, said of the whole number a step names
for that term: any two whole numbers the term is are one. -/
theorem parley_witness_at {K : Type*} [AddGroupWithOne K] [CharZero K] {t : K}
    {P : ℤ → Prop} (h : ∃ m : ℤ, (m : K) = t ∧ P m) (w : ℤ) (hw : (w : K) = t) :
    P w := by
  obtain ⟨m, hm, hp⟩ := h
  have : m = w := Int.cast_injective (hm.trans hw.symm)
  exact this ▸ hp

/-- `parley_witness_at` of a natural number. -/
theorem parley_witness_at_nat {K : Type*} [AddMonoidWithOne K] [CharZero K] {t : K}
    {P : ℕ → Prop} (h : ∃ m : ℕ, (m : K) = t ∧ P m) (w : ℕ) (hw : (w : K) = t) :
    P w := by
  obtain ⟨m, hm, hp⟩ := h
  have : m = w := Nat.cast_injective (hm.trans hw.symm)
  exact this ▸ hp

/-- A line that no whole number is t with P, `¬ ∃ m : ℤ, ↑m = t ∧ P m`,
said of the number a step names for t: P does not hold of it. -/
theorem parley_witness_not_at {K : Type*} [AddGroupWithOne K] [CharZero K] {t : K}
    {P : ℤ → Prop} (h : ¬ ∃ m : ℤ, (m : K) = t ∧ P m) (w : ℤ) (hw : (w : K) = t) :
    ¬ P w :=
  fun hp => h ⟨w, hw, hp⟩

/-- `parley_witness_not_at` of a natural number. -/
theorem parley_witness_not_at_nat {K : Type*} [AddMonoidWithOne K] [CharZero K] {t : K}
    {P : ℕ → Prop} (h : ¬ ∃ m : ℕ, (m : K) = t ∧ P m) (w : ℕ) (hw : (w : K) = t) :
    ¬ P w :=
  fun hp => h ⟨w, hw, hp⟩

end
