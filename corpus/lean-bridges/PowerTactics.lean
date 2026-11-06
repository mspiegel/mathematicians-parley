module

public import Mathlib
public import Tactics

/-!
# Natural numbers given as an integer's `toNat`

Where the page's natural number is an integer a line shows not negative,
the build writes its `toNat`: `parley_cast_toNat` casts it back, and
`parley_int_power` reads an item's natural exponents at the claim's integer
ones. A generated file imports this module only when it names one of them.
-/

public section

/-- An integer power to an exponent at least 0 is the natural power to its
`toNat`: a line of a field, (−1)^n in ℚ, said where the claim is of
integers, (−1)^(n.toNat) in ℤ, which has no integer powers. -/
theorem parley_zpow_toNat {K : Type*} [DivisionRing K] (a : K) (n : ℤ) (h : 0 ≤ n) :
    a ^ n = a ^ n.toNat := by
  rw [← zpow_natCast, Int.toNat_of_nonneg h]

/-- The line `h`, its natural powers to an integer's `toNat`, 2^(d·e).toNat
of an item whose letters are in ℕ, said where the claim has the integer
power 2^(d·e), its exponent at least 0 by the lines in scope: the claim's
powers taken to natural ones and `h` used, cast as the claim is. -/
macro "parley_line_toNat " h:term:max : tactic =>
  `(tactic| first
    | (simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat];
        exact_mod_cast $h:term; done)
    | (simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat];
        push_cast; linear_combination (norm := parley_norm) $h:term; done))

/-- An integer not negative, cast to any ring from the natural number its
`toNat` is, is itself: the build gives a natural letter an integer the page
shows is not negative as its `toNat` (`theorem::witness`). -/
theorem parley_cast_toNat {R : Type*} [Ring R] {n : ℤ} (h : 0 ≤ n) :
    ((n.toNat : ℕ) : R) = (n : R) := by
  rw [← Int.cast_natCast, Int.toNat_of_nonneg h]

/-- An equation `h` an item gives of natural exponents, given an integer's
`toNat` for one, read at the claim's integer exponents: 2^(n − 1 + 1) with
n − 1 an integer that a line shows not negative, which `omega` proves. An
equation of integers is taken to ℚ first, where integer powers are. -/
macro "parley_int_power " h:ident : tactic =>
  `(tactic| first
    | (simp (disch := omega) only [← zpow_natCast, Nat.cast_add, Nat.cast_one,
        Int.toNat_of_nonneg] at $h:ident;
        first
          | (linear_combination (norm := parley_norm) ($h:ident); done)
          -- The claim is the equation turned round.
          | (linear_combination (norm := parley_norm) (-$h:ident); done))
    -- The claim's own natural exponents read as integers too, p^a beside
    -- p^(a′ − a), so that each power is one integer power on both sides.
    | (simp (disch := omega) only [← zpow_natCast, Nat.cast_add, Nat.cast_one,
        Int.toNat_of_nonneg] at $h:ident ⊢;
        linear_combination (norm := parley_norm) ($h:ident); done)
    -- Taken to ℚ, the goal with it: the integer brought back from its
    -- `toNat` may stand as `Int.subNatNat n 1`, which is n − 1.
    | (have q := congrArg (fun x : ℤ => (x : ℚ)) $h:ident; push_cast at q;
        simp (disch := omega) only [Int.subNatNat_eq_coe, ← zpow_natCast, Nat.cast_add,
        Nat.cast_one, Int.toNat_of_nonneg] at q ⊢;
        linear_combination (norm := parley_norm) q; done)
    -- A claim in ℤ whose own exponents are integers' `toNat`s, p^(a′ − a)
    -- beside p^a: the claim taken to ℚ too, where each such power is the
    -- integer power it is.
    | (have q := congrArg (fun x : ℤ => (x : ℚ)) $h:ident; push_cast at q; qify;
        simp (disch := omega) only [Int.subNatNat_eq_coe, ← zpow_natCast, Nat.cast_add,
        Nat.cast_one, Int.toNat_of_nonneg] at q ⊢;
        linear_combination (norm := parley_norm) q; done))

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
