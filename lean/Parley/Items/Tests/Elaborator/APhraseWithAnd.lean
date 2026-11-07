module

public import Tactics
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq

/-! Written from tests/elaborator/a-phrase-with-and.proof by parley build lean. -/

public section

namespace Parley.Items.Tests.Elaborator.APhraseWithAnd

theorem def_common_divisor (a : ℂ) (b : ℂ) (d : ℂ) :
    ((∃ m : ℤ, (m : ℂ) = d) ∧ (∃ m : ℤ, (m : ℂ) = d ∧ (∃ m₀ : ℤ, (m₀ : ℂ) = a ∧ m ∣ m₀))) ∧ (∃ m : ℤ, (m : ℂ) = d ∧ (∃ m₀ : ℤ, (m₀ : ℂ) = b ∧ m ∣ m₀)) ↔ ((∃ m : ℤ, (m : ℂ) = d) ∧ (∃ m : ℤ, (m : ℂ) = d ∧ (∃ m₀ : ℤ, (m₀ : ℂ) = a ∧ m ∣ m₀))) ∧ (∃ m : ℤ, (m : ℂ) = d ∧ (∃ m₀ : ℤ, (m₀ : ℂ) = b ∧ m ∣ m₀)) :=
  Iff.rfl

end Parley.Items.Tests.Elaborator.APhraseWithAnd
