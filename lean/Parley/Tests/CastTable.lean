module

public import Mathlib

/-! Written from the cast table (`src/lean/casts.rs`) by parley build lean. -/

public section

set_option linter.unusedTactic false

namespace Parley.Tests.CastTable

-- Add ℕ to ℤ: push_cast moves, norm_cast moves
example (a b : ℕ) : ((a + b : ℕ) : ℤ) = (a : ℤ) + (b : ℤ) := by push_cast; try rfl
example (a b : ℕ) : ((a + b : ℕ) : ℤ) = (a : ℤ) + (b : ℤ) := by norm_cast

-- Add ℕ to ℚ: push_cast moves, norm_cast moves
example (a b : ℕ) : ((a + b : ℕ) : ℚ) = (a : ℚ) + (b : ℚ) := by push_cast; try rfl
example (a b : ℕ) : ((a + b : ℕ) : ℚ) = (a : ℚ) + (b : ℚ) := by norm_cast

-- Add ℕ to ℝ: push_cast moves, norm_cast moves
example (a b : ℕ) : ((a + b : ℕ) : ℝ) = (a : ℝ) + (b : ℝ) := by push_cast; try rfl
example (a b : ℕ) : ((a + b : ℕ) : ℝ) = (a : ℝ) + (b : ℝ) := by norm_cast

-- Add ℕ to ℂ: push_cast moves, norm_cast moves
example (a b : ℕ) : ((a + b : ℕ) : ℂ) = (a : ℂ) + (b : ℂ) := by push_cast; try rfl
example (a b : ℕ) : ((a + b : ℕ) : ℂ) = (a : ℂ) + (b : ℂ) := by norm_cast

-- Add ℤ to ℚ: push_cast moves, norm_cast moves
example (a b : ℤ) : ((a + b : ℤ) : ℚ) = (a : ℚ) + (b : ℚ) := by push_cast; try rfl
example (a b : ℤ) : ((a + b : ℤ) : ℚ) = (a : ℚ) + (b : ℚ) := by norm_cast

-- Add ℤ to ℝ: push_cast moves, norm_cast moves
example (a b : ℤ) : ((a + b : ℤ) : ℝ) = (a : ℝ) + (b : ℝ) := by push_cast; try rfl
example (a b : ℤ) : ((a + b : ℤ) : ℝ) = (a : ℝ) + (b : ℝ) := by norm_cast

-- Add ℤ to ℂ: push_cast moves, norm_cast moves
example (a b : ℤ) : ((a + b : ℤ) : ℂ) = (a : ℂ) + (b : ℂ) := by push_cast; try rfl
example (a b : ℤ) : ((a + b : ℤ) : ℂ) = (a : ℂ) + (b : ℂ) := by norm_cast

-- Add ℚ to ℝ: push_cast moves, norm_cast moves
example (a b : ℚ) : ((a + b : ℚ) : ℝ) = (a : ℝ) + (b : ℝ) := by push_cast; try rfl
example (a b : ℚ) : ((a + b : ℚ) : ℝ) = (a : ℝ) + (b : ℝ) := by norm_cast

-- Add ℚ to ℂ: push_cast moves, norm_cast moves
example (a b : ℚ) : ((a + b : ℚ) : ℂ) = (a : ℂ) + (b : ℂ) := by push_cast; try rfl
example (a b : ℚ) : ((a + b : ℚ) : ℂ) = (a : ℂ) + (b : ℂ) := by norm_cast

-- Add ℝ to ℂ: push_cast moves, norm_cast moves
example (a b : ℝ) : ((a + b : ℝ) : ℂ) = (a : ℂ) + (b : ℂ) := by push_cast; try rfl
example (a b : ℝ) : ((a + b : ℝ) : ℂ) = (a : ℂ) + (b : ℂ) := by norm_cast

-- Add ℕ to ℕ∞: push_cast moves, norm_cast moves
example (a b : ℕ) : ((a + b : ℕ) : ℕ∞) = (a : ℕ∞) + (b : ℕ∞) := by push_cast; try rfl
example (a b : ℕ) : ((a + b : ℕ) : ℕ∞) = (a : ℕ∞) + (b : ℕ∞) := by norm_cast

-- Sub ℤ to ℚ: push_cast moves, norm_cast moves
example (a b : ℤ) : ((a - b : ℤ) : ℚ) = (a : ℚ) - (b : ℚ) := by push_cast; try rfl
example (a b : ℤ) : ((a - b : ℤ) : ℚ) = (a : ℚ) - (b : ℚ) := by norm_cast

-- Sub ℤ to ℝ: push_cast moves, norm_cast moves
example (a b : ℤ) : ((a - b : ℤ) : ℝ) = (a : ℝ) - (b : ℝ) := by push_cast; try rfl
example (a b : ℤ) : ((a - b : ℤ) : ℝ) = (a : ℝ) - (b : ℝ) := by norm_cast

-- Sub ℤ to ℂ: push_cast moves, norm_cast moves
example (a b : ℤ) : ((a - b : ℤ) : ℂ) = (a : ℂ) - (b : ℂ) := by push_cast; try rfl
example (a b : ℤ) : ((a - b : ℤ) : ℂ) = (a : ℂ) - (b : ℂ) := by norm_cast

-- Sub ℚ to ℝ: push_cast moves, norm_cast moves
example (a b : ℚ) : ((a - b : ℚ) : ℝ) = (a : ℝ) - (b : ℝ) := by push_cast; try rfl
example (a b : ℚ) : ((a - b : ℚ) : ℝ) = (a : ℝ) - (b : ℝ) := by norm_cast

-- Sub ℚ to ℂ: push_cast moves, norm_cast moves
example (a b : ℚ) : ((a - b : ℚ) : ℂ) = (a : ℂ) - (b : ℂ) := by push_cast; try rfl
example (a b : ℚ) : ((a - b : ℚ) : ℂ) = (a : ℂ) - (b : ℂ) := by norm_cast

-- Sub ℝ to ℂ: push_cast moves, norm_cast moves
example (a b : ℝ) : ((a - b : ℝ) : ℂ) = (a : ℂ) - (b : ℂ) := by push_cast; try rfl
example (a b : ℝ) : ((a - b : ℝ) : ℂ) = (a : ℂ) - (b : ℂ) := by norm_cast

-- Mul ℕ to ℤ: push_cast moves, norm_cast moves
example (a b : ℕ) : ((a * b : ℕ) : ℤ) = (a : ℤ) * (b : ℤ) := by push_cast; try rfl
example (a b : ℕ) : ((a * b : ℕ) : ℤ) = (a : ℤ) * (b : ℤ) := by norm_cast

-- Mul ℕ to ℚ: push_cast moves, norm_cast moves
example (a b : ℕ) : ((a * b : ℕ) : ℚ) = (a : ℚ) * (b : ℚ) := by push_cast; try rfl
example (a b : ℕ) : ((a * b : ℕ) : ℚ) = (a : ℚ) * (b : ℚ) := by norm_cast

-- Mul ℕ to ℝ: push_cast moves, norm_cast moves
example (a b : ℕ) : ((a * b : ℕ) : ℝ) = (a : ℝ) * (b : ℝ) := by push_cast; try rfl
example (a b : ℕ) : ((a * b : ℕ) : ℝ) = (a : ℝ) * (b : ℝ) := by norm_cast

-- Mul ℕ to ℂ: push_cast moves, norm_cast moves
example (a b : ℕ) : ((a * b : ℕ) : ℂ) = (a : ℂ) * (b : ℂ) := by push_cast; try rfl
example (a b : ℕ) : ((a * b : ℕ) : ℂ) = (a : ℂ) * (b : ℂ) := by norm_cast

-- Mul ℤ to ℚ: push_cast moves, norm_cast moves
example (a b : ℤ) : ((a * b : ℤ) : ℚ) = (a : ℚ) * (b : ℚ) := by push_cast; try rfl
example (a b : ℤ) : ((a * b : ℤ) : ℚ) = (a : ℚ) * (b : ℚ) := by norm_cast

-- Mul ℤ to ℝ: push_cast moves, norm_cast moves
example (a b : ℤ) : ((a * b : ℤ) : ℝ) = (a : ℝ) * (b : ℝ) := by push_cast; try rfl
example (a b : ℤ) : ((a * b : ℤ) : ℝ) = (a : ℝ) * (b : ℝ) := by norm_cast

-- Mul ℤ to ℂ: push_cast moves, norm_cast moves
example (a b : ℤ) : ((a * b : ℤ) : ℂ) = (a : ℂ) * (b : ℂ) := by push_cast; try rfl
example (a b : ℤ) : ((a * b : ℤ) : ℂ) = (a : ℂ) * (b : ℂ) := by norm_cast

-- Mul ℚ to ℝ: push_cast moves, norm_cast moves
example (a b : ℚ) : ((a * b : ℚ) : ℝ) = (a : ℝ) * (b : ℝ) := by push_cast; try rfl
example (a b : ℚ) : ((a * b : ℚ) : ℝ) = (a : ℝ) * (b : ℝ) := by norm_cast

-- Mul ℚ to ℂ: push_cast moves, norm_cast moves
example (a b : ℚ) : ((a * b : ℚ) : ℂ) = (a : ℂ) * (b : ℂ) := by push_cast; try rfl
example (a b : ℚ) : ((a * b : ℚ) : ℂ) = (a : ℂ) * (b : ℂ) := by norm_cast

-- Mul ℝ to ℂ: push_cast moves, norm_cast moves
example (a b : ℝ) : ((a * b : ℝ) : ℂ) = (a : ℂ) * (b : ℂ) := by push_cast; try rfl
example (a b : ℝ) : ((a * b : ℝ) : ℂ) = (a : ℂ) * (b : ℂ) := by norm_cast

-- Div ℚ to ℝ: push_cast moves, norm_cast moves
example (a b : ℚ) : ((a / b : ℚ) : ℝ) = (a : ℝ) / (b : ℝ) := by push_cast; try rfl
example (a b : ℚ) : ((a / b : ℚ) : ℝ) = (a : ℝ) / (b : ℝ) := by norm_cast

-- Div ℚ to ℂ: push_cast moves, norm_cast moves
example (a b : ℚ) : ((a / b : ℚ) : ℂ) = (a : ℂ) / (b : ℂ) := by push_cast; try rfl
example (a b : ℚ) : ((a / b : ℚ) : ℂ) = (a : ℂ) / (b : ℂ) := by norm_cast

-- Div ℝ to ℂ: push_cast moves, norm_cast moves
example (a b : ℝ) : ((a / b : ℝ) : ℂ) = (a : ℂ) / (b : ℂ) := by push_cast; try rfl
example (a b : ℝ) : ((a / b : ℝ) : ℂ) = (a : ℂ) / (b : ℂ) := by norm_cast

-- Neg ℤ to ℚ: push_cast moves, norm_cast moves
example (a : ℤ) : ((-a : ℤ) : ℚ) = -(a : ℚ) := by push_cast; try rfl
example (a : ℤ) : ((-a : ℤ) : ℚ) = -(a : ℚ) := by norm_cast

-- Neg ℤ to ℝ: push_cast moves, norm_cast moves
example (a : ℤ) : ((-a : ℤ) : ℝ) = -(a : ℝ) := by push_cast; try rfl
example (a : ℤ) : ((-a : ℤ) : ℝ) = -(a : ℝ) := by norm_cast

-- Neg ℤ to ℂ: push_cast moves, norm_cast moves
example (a : ℤ) : ((-a : ℤ) : ℂ) = -(a : ℂ) := by push_cast; try rfl
example (a : ℤ) : ((-a : ℤ) : ℂ) = -(a : ℂ) := by norm_cast

-- Neg ℚ to ℝ: push_cast moves, norm_cast moves
example (a : ℚ) : ((-a : ℚ) : ℝ) = -(a : ℝ) := by push_cast; try rfl
example (a : ℚ) : ((-a : ℚ) : ℝ) = -(a : ℝ) := by norm_cast

-- Neg ℚ to ℂ: push_cast moves, norm_cast moves
example (a : ℚ) : ((-a : ℚ) : ℂ) = -(a : ℂ) := by push_cast; try rfl
example (a : ℚ) : ((-a : ℚ) : ℂ) = -(a : ℂ) := by norm_cast

-- Neg ℝ to ℂ: push_cast moves, norm_cast moves
example (a : ℝ) : ((-a : ℝ) : ℂ) = -(a : ℂ) := by push_cast; try rfl
example (a : ℝ) : ((-a : ℝ) : ℂ) = -(a : ℂ) := by norm_cast

-- NatPow ℕ to ℤ: push_cast moves, norm_cast moves
example (a : ℕ) (n : ℕ) : ((a ^ n : ℕ) : ℤ) = (a : ℤ) ^ n := by push_cast; try rfl
example (a : ℕ) (n : ℕ) : ((a ^ n : ℕ) : ℤ) = (a : ℤ) ^ n := by norm_cast

-- NatPow ℕ to ℚ: push_cast moves, norm_cast moves
example (a : ℕ) (n : ℕ) : ((a ^ n : ℕ) : ℚ) = (a : ℚ) ^ n := by push_cast; try rfl
example (a : ℕ) (n : ℕ) : ((a ^ n : ℕ) : ℚ) = (a : ℚ) ^ n := by norm_cast

-- NatPow ℕ to ℝ: push_cast moves, norm_cast moves
example (a : ℕ) (n : ℕ) : ((a ^ n : ℕ) : ℝ) = (a : ℝ) ^ n := by push_cast; try rfl
example (a : ℕ) (n : ℕ) : ((a ^ n : ℕ) : ℝ) = (a : ℝ) ^ n := by norm_cast

-- NatPow ℕ to ℂ: push_cast moves, norm_cast moves
example (a : ℕ) (n : ℕ) : ((a ^ n : ℕ) : ℂ) = (a : ℂ) ^ n := by push_cast; try rfl
example (a : ℕ) (n : ℕ) : ((a ^ n : ℕ) : ℂ) = (a : ℂ) ^ n := by norm_cast

-- NatPow ℤ to ℚ: push_cast moves, norm_cast moves
example (a : ℤ) (n : ℕ) : ((a ^ n : ℤ) : ℚ) = (a : ℚ) ^ n := by push_cast; try rfl
example (a : ℤ) (n : ℕ) : ((a ^ n : ℤ) : ℚ) = (a : ℚ) ^ n := by norm_cast

-- NatPow ℤ to ℝ: push_cast moves, norm_cast moves
example (a : ℤ) (n : ℕ) : ((a ^ n : ℤ) : ℝ) = (a : ℝ) ^ n := by push_cast; try rfl
example (a : ℤ) (n : ℕ) : ((a ^ n : ℤ) : ℝ) = (a : ℝ) ^ n := by norm_cast

-- NatPow ℤ to ℂ: push_cast moves, norm_cast moves
example (a : ℤ) (n : ℕ) : ((a ^ n : ℤ) : ℂ) = (a : ℂ) ^ n := by push_cast; try rfl
example (a : ℤ) (n : ℕ) : ((a ^ n : ℤ) : ℂ) = (a : ℂ) ^ n := by norm_cast

-- NatPow ℚ to ℝ: push_cast moves, norm_cast moves
example (a : ℚ) (n : ℕ) : ((a ^ n : ℚ) : ℝ) = (a : ℝ) ^ n := by push_cast; try rfl
example (a : ℚ) (n : ℕ) : ((a ^ n : ℚ) : ℝ) = (a : ℝ) ^ n := by norm_cast

-- NatPow ℚ to ℂ: push_cast moves, norm_cast moves
example (a : ℚ) (n : ℕ) : ((a ^ n : ℚ) : ℂ) = (a : ℂ) ^ n := by push_cast; try rfl
example (a : ℚ) (n : ℕ) : ((a ^ n : ℚ) : ℂ) = (a : ℂ) ^ n := by norm_cast

-- NatPow ℝ to ℂ: push_cast moves, norm_cast moves
example (a : ℝ) (n : ℕ) : ((a ^ n : ℝ) : ℂ) = (a : ℂ) ^ n := by push_cast; try rfl
example (a : ℝ) (n : ℕ) : ((a ^ n : ℝ) : ℂ) = (a : ℂ) ^ n := by norm_cast

-- IntPow ℚ to ℝ: push_cast moves, norm_cast moves
example (a : ℚ) (k : ℤ) : ((a ^ k : ℚ) : ℝ) = (a : ℝ) ^ k := by push_cast; try rfl
example (a : ℚ) (k : ℤ) : ((a ^ k : ℚ) : ℝ) = (a : ℝ) ^ k := by norm_cast

-- IntPow ℚ to ℂ: push_cast moves, norm_cast moves
example (a : ℚ) (k : ℤ) : ((a ^ k : ℚ) : ℂ) = (a : ℂ) ^ k := by push_cast; try rfl
example (a : ℚ) (k : ℤ) : ((a ^ k : ℚ) : ℂ) = (a : ℂ) ^ k := by norm_cast

-- IntPow ℝ to ℂ: push_cast moves, norm_cast moves
example (a : ℝ) (k : ℤ) : ((a ^ k : ℝ) : ℂ) = (a : ℂ) ^ k := by push_cast; try rfl
example (a : ℝ) (k : ℤ) : ((a ^ k : ℝ) : ℂ) = (a : ℂ) ^ k := by norm_cast

-- Abs ℤ to ℚ: push_cast moves, norm_cast moves
example (a : ℤ) : ((|a| : ℤ) : ℚ) = |(a : ℚ)| := by push_cast; try rfl
example (a : ℤ) : ((|a| : ℤ) : ℚ) = |(a : ℚ)| := by norm_cast

-- Abs ℤ to ℝ: push_cast moves, norm_cast moves
example (a : ℤ) : ((|a| : ℤ) : ℝ) = |(a : ℝ)| := by push_cast; try rfl
example (a : ℤ) : ((|a| : ℤ) : ℝ) = |(a : ℝ)| := by norm_cast

-- Abs ℚ to ℝ: push_cast moves, norm_cast moves
example (a : ℚ) : ((|a| : ℚ) : ℝ) = |(a : ℝ)| := by push_cast; try rfl
example (a : ℚ) : ((|a| : ℚ) : ℝ) = |(a : ℝ)| := by norm_cast

-- Norm ℝ to ℂ: push_cast stops, norm_cast moves
example : True := by
  fail_if_success (have : ∀ (a : ℝ), ((|a| : ℝ) : ℝ) = ‖(a : ℂ)‖ := by intro a; push_cast; try rfl)
  trivial
example (a : ℝ) : ((|a| : ℝ) : ℝ) = ‖(a : ℂ)‖ := by norm_cast

-- RealPow ℝ to ℂ: push_cast stops, norm_cast stops
example : True := by
  fail_if_success (have : ∀ (a b : ℝ), ((a ^ b : ℝ) : ℂ) = (a : ℂ) ^ (b : ℂ) := by intro a b; push_cast; try rfl)
  trivial
example : True := by
  fail_if_success (have : ∀ (a b : ℝ), ((a ^ b : ℝ) : ℂ) = (a : ℂ) ^ (b : ℂ) := by intro a b; norm_cast)
  trivial

-- Sqrt ℝ to ℂ: push_cast stops, norm_cast stops
example : True := by
  fail_if_success (have : ∀ (a : ℝ), ((Real.sqrt a : ℝ) : ℂ) = (a : ℂ) ^ ((1 : ℂ) / 2) := by intro a; push_cast; try rfl)
  trivial
example : True := by
  fail_if_success (have : ∀ (a : ℝ), ((Real.sqrt a : ℝ) : ℂ) = (a : ℂ) ^ ((1 : ℂ) / 2) := by intro a; norm_cast)
  trivial

-- Exp ℝ to ℂ: push_cast moves, norm_cast moves
example (a : ℝ) : ((Real.exp a : ℝ) : ℂ) = Complex.exp (a : ℂ) := by push_cast; try rfl
example (a : ℝ) : ((Real.exp a : ℝ) : ℂ) = Complex.exp (a : ℂ) := by norm_cast

-- Log ℝ to ℂ: push_cast stops, norm_cast stops
example : True := by
  fail_if_success (have : ∀ (a : ℝ), ((Real.log a : ℝ) : ℂ) = Complex.log (a : ℂ) := by intro a; push_cast; try rfl)
  trivial
example : True := by
  fail_if_success (have : ∀ (a : ℝ), ((Real.log a : ℝ) : ℂ) = Complex.log (a : ℂ) := by intro a; norm_cast)
  trivial

-- Sin ℝ to ℂ: push_cast moves, norm_cast moves
example (a : ℝ) : ((Real.sin a : ℝ) : ℂ) = Complex.sin (a : ℂ) := by push_cast; try rfl
example (a : ℝ) : ((Real.sin a : ℝ) : ℂ) = Complex.sin (a : ℂ) := by norm_cast

-- Cos ℝ to ℂ: push_cast moves, norm_cast moves
example (a : ℝ) : ((Real.cos a : ℝ) : ℂ) = Complex.cos (a : ℂ) := by push_cast; try rfl
example (a : ℝ) : ((Real.cos a : ℝ) : ℂ) = Complex.cos (a : ℂ) := by norm_cast

-- Floor ℚ to ℝ: push_cast stops, norm_cast moves
example : True := by
  fail_if_success (have : ∀ (a : ℚ), (⌊a⌋ : ℤ) = ⌊(a : ℝ)⌋ := by intro a; push_cast; try rfl)
  trivial
example (a : ℚ) : (⌊a⌋ : ℤ) = ⌊(a : ℝ)⌋ := by norm_cast

-- ToNat ℕ to ℤ: push_cast moves, norm_cast moves
example (a : ℕ) : ((a : ℕ) : ℤ).toNat = a := by push_cast; try rfl
example (a : ℕ) : ((a : ℕ) : ℤ).toNat = a := by norm_cast

-- Sum ℕ to ℤ: push_cast moves, norm_cast moves
example (s : Finset ℕ) (f : ℕ → ℕ) : ((∑ i ∈ s, f i : ℕ) : ℤ) = ∑ i ∈ s, (f i : ℤ) := by push_cast; try rfl
example (s : Finset ℕ) (f : ℕ → ℕ) : ((∑ i ∈ s, f i : ℕ) : ℤ) = ∑ i ∈ s, (f i : ℤ) := by norm_cast

-- Sum ℕ to ℚ: push_cast moves, norm_cast moves
example (s : Finset ℕ) (f : ℕ → ℕ) : ((∑ i ∈ s, f i : ℕ) : ℚ) = ∑ i ∈ s, (f i : ℚ) := by push_cast; try rfl
example (s : Finset ℕ) (f : ℕ → ℕ) : ((∑ i ∈ s, f i : ℕ) : ℚ) = ∑ i ∈ s, (f i : ℚ) := by norm_cast

-- Sum ℕ to ℝ: push_cast moves, norm_cast moves
example (s : Finset ℕ) (f : ℕ → ℕ) : ((∑ i ∈ s, f i : ℕ) : ℝ) = ∑ i ∈ s, (f i : ℝ) := by push_cast; try rfl
example (s : Finset ℕ) (f : ℕ → ℕ) : ((∑ i ∈ s, f i : ℕ) : ℝ) = ∑ i ∈ s, (f i : ℝ) := by norm_cast

-- Sum ℕ to ℂ: push_cast moves, norm_cast moves
example (s : Finset ℕ) (f : ℕ → ℕ) : ((∑ i ∈ s, f i : ℕ) : ℂ) = ∑ i ∈ s, (f i : ℂ) := by push_cast; try rfl
example (s : Finset ℕ) (f : ℕ → ℕ) : ((∑ i ∈ s, f i : ℕ) : ℂ) = ∑ i ∈ s, (f i : ℂ) := by norm_cast

-- Sum ℤ to ℚ: push_cast moves, norm_cast moves
example (s : Finset ℕ) (f : ℕ → ℤ) : ((∑ i ∈ s, f i : ℤ) : ℚ) = ∑ i ∈ s, (f i : ℚ) := by push_cast; try rfl
example (s : Finset ℕ) (f : ℕ → ℤ) : ((∑ i ∈ s, f i : ℤ) : ℚ) = ∑ i ∈ s, (f i : ℚ) := by norm_cast

-- Sum ℤ to ℝ: push_cast moves, norm_cast moves
example (s : Finset ℕ) (f : ℕ → ℤ) : ((∑ i ∈ s, f i : ℤ) : ℝ) = ∑ i ∈ s, (f i : ℝ) := by push_cast; try rfl
example (s : Finset ℕ) (f : ℕ → ℤ) : ((∑ i ∈ s, f i : ℤ) : ℝ) = ∑ i ∈ s, (f i : ℝ) := by norm_cast

-- Sum ℤ to ℂ: push_cast moves, norm_cast moves
example (s : Finset ℕ) (f : ℕ → ℤ) : ((∑ i ∈ s, f i : ℤ) : ℂ) = ∑ i ∈ s, (f i : ℂ) := by push_cast; try rfl
example (s : Finset ℕ) (f : ℕ → ℤ) : ((∑ i ∈ s, f i : ℤ) : ℂ) = ∑ i ∈ s, (f i : ℂ) := by norm_cast

-- Sum ℚ to ℝ: push_cast moves, norm_cast moves
example (s : Finset ℕ) (f : ℕ → ℚ) : ((∑ i ∈ s, f i : ℚ) : ℝ) = ∑ i ∈ s, (f i : ℝ) := by push_cast; try rfl
example (s : Finset ℕ) (f : ℕ → ℚ) : ((∑ i ∈ s, f i : ℚ) : ℝ) = ∑ i ∈ s, (f i : ℝ) := by norm_cast

-- Sum ℚ to ℂ: push_cast moves, norm_cast moves
example (s : Finset ℕ) (f : ℕ → ℚ) : ((∑ i ∈ s, f i : ℚ) : ℂ) = ∑ i ∈ s, (f i : ℂ) := by push_cast; try rfl
example (s : Finset ℕ) (f : ℕ → ℚ) : ((∑ i ∈ s, f i : ℚ) : ℂ) = ∑ i ∈ s, (f i : ℂ) := by norm_cast

-- Sum ℝ to ℂ: push_cast moves, norm_cast moves
example (s : Finset ℕ) (f : ℕ → ℝ) : ((∑ i ∈ s, f i : ℝ) : ℂ) = ∑ i ∈ s, (f i : ℂ) := by push_cast; try rfl
example (s : Finset ℕ) (f : ℕ → ℝ) : ((∑ i ∈ s, f i : ℝ) : ℂ) = ∑ i ∈ s, (f i : ℂ) := by norm_cast

-- NumeralQuotient ℤ to ℚ: push_cast moves, norm_cast stops
example (x : ℤ) : ((1 : ℤ) : ℚ) / 3 ≤ (x : ℚ) → (1 : ℚ) / 3 ≤ (x : ℚ) := by intro h; push_cast at h ⊢; exact h
example : True := by
  fail_if_success (have : ∀ (x : ℤ), ((1 : ℤ) : ℚ) / 3 ≤ (x : ℚ) → (1 : ℚ) / 3 ≤ (x : ℚ) := by intro x; intro h; exact_mod_cast h)
  trivial

-- NumeralQuotient ℤ to ℝ: push_cast moves, norm_cast stops
example (x : ℤ) : ((1 : ℤ) : ℝ) / 3 ≤ (x : ℝ) → (1 : ℝ) / 3 ≤ (x : ℝ) := by intro h; push_cast at h ⊢; exact h
example : True := by
  fail_if_success (have : ∀ (x : ℤ), ((1 : ℤ) : ℝ) / 3 ≤ (x : ℝ) → (1 : ℝ) / 3 ≤ (x : ℝ) := by intro x; intro h; exact_mod_cast h)
  trivial

-- NumeralQuotient ℚ to ℝ: push_cast moves, norm_cast stops
example (x : ℚ) : ((1 : ℚ) : ℝ) / 3 ≤ (x : ℝ) → (1 : ℝ) / 3 ≤ (x : ℝ) := by intro h; push_cast at h ⊢; exact h
example : True := by
  fail_if_success (have : ∀ (x : ℚ), ((1 : ℚ) : ℝ) / 3 ≤ (x : ℝ) → (1 : ℝ) / 3 ≤ (x : ℝ) := by intro x; intro h; exact_mod_cast h)
  trivial

-- Eq ℕ to ℤ: push_cast stops, norm_cast moves
example : True := by
  fail_if_success (have : ∀ (a b : ℕ), ((a : ℕ) : ℤ) = ((b : ℕ) : ℤ) ↔ a = b := by intro a b; push_cast; try rfl)
  trivial
example (a b : ℕ) : ((a : ℕ) : ℤ) = ((b : ℕ) : ℤ) ↔ a = b := by norm_cast

-- Eq ℕ to ℚ: push_cast stops, norm_cast moves
example : True := by
  fail_if_success (have : ∀ (a b : ℕ), ((a : ℕ) : ℚ) = ((b : ℕ) : ℚ) ↔ a = b := by intro a b; push_cast; try rfl)
  trivial
example (a b : ℕ) : ((a : ℕ) : ℚ) = ((b : ℕ) : ℚ) ↔ a = b := by norm_cast

-- Eq ℕ to ℝ: push_cast stops, norm_cast moves
example : True := by
  fail_if_success (have : ∀ (a b : ℕ), ((a : ℕ) : ℝ) = ((b : ℕ) : ℝ) ↔ a = b := by intro a b; push_cast; try rfl)
  trivial
example (a b : ℕ) : ((a : ℕ) : ℝ) = ((b : ℕ) : ℝ) ↔ a = b := by norm_cast

-- Eq ℕ to ℂ: push_cast stops, norm_cast moves
example : True := by
  fail_if_success (have : ∀ (a b : ℕ), ((a : ℕ) : ℂ) = ((b : ℕ) : ℂ) ↔ a = b := by intro a b; push_cast; try rfl)
  trivial
example (a b : ℕ) : ((a : ℕ) : ℂ) = ((b : ℕ) : ℂ) ↔ a = b := by norm_cast

-- Eq ℤ to ℚ: push_cast stops, norm_cast moves
example : True := by
  fail_if_success (have : ∀ (a b : ℤ), ((a : ℤ) : ℚ) = ((b : ℤ) : ℚ) ↔ a = b := by intro a b; push_cast; try rfl)
  trivial
example (a b : ℤ) : ((a : ℤ) : ℚ) = ((b : ℤ) : ℚ) ↔ a = b := by norm_cast

-- Eq ℤ to ℝ: push_cast stops, norm_cast moves
example : True := by
  fail_if_success (have : ∀ (a b : ℤ), ((a : ℤ) : ℝ) = ((b : ℤ) : ℝ) ↔ a = b := by intro a b; push_cast; try rfl)
  trivial
example (a b : ℤ) : ((a : ℤ) : ℝ) = ((b : ℤ) : ℝ) ↔ a = b := by norm_cast

-- Eq ℤ to ℂ: push_cast stops, norm_cast moves
example : True := by
  fail_if_success (have : ∀ (a b : ℤ), ((a : ℤ) : ℂ) = ((b : ℤ) : ℂ) ↔ a = b := by intro a b; push_cast; try rfl)
  trivial
example (a b : ℤ) : ((a : ℤ) : ℂ) = ((b : ℤ) : ℂ) ↔ a = b := by norm_cast

-- Eq ℚ to ℝ: push_cast stops, norm_cast moves
example : True := by
  fail_if_success (have : ∀ (a b : ℚ), ((a : ℚ) : ℝ) = ((b : ℚ) : ℝ) ↔ a = b := by intro a b; push_cast; try rfl)
  trivial
example (a b : ℚ) : ((a : ℚ) : ℝ) = ((b : ℚ) : ℝ) ↔ a = b := by norm_cast

-- Eq ℚ to ℂ: push_cast stops, norm_cast moves
example : True := by
  fail_if_success (have : ∀ (a b : ℚ), ((a : ℚ) : ℂ) = ((b : ℚ) : ℂ) ↔ a = b := by intro a b; push_cast; try rfl)
  trivial
example (a b : ℚ) : ((a : ℚ) : ℂ) = ((b : ℚ) : ℂ) ↔ a = b := by norm_cast

-- Eq ℝ to ℂ: push_cast stops, norm_cast moves
example : True := by
  fail_if_success (have : ∀ (a b : ℝ), ((a : ℝ) : ℂ) = ((b : ℝ) : ℂ) ↔ a = b := by intro a b; push_cast; try rfl)
  trivial
example (a b : ℝ) : ((a : ℝ) : ℂ) = ((b : ℝ) : ℂ) ↔ a = b := by norm_cast

-- Eq ℕ to ℕ∞: push_cast stops, norm_cast moves
example : True := by
  fail_if_success (have : ∀ (a b : ℕ), ((a : ℕ) : ℕ∞) = ((b : ℕ) : ℕ∞) ↔ a = b := by intro a b; push_cast; try rfl)
  trivial
example (a b : ℕ) : ((a : ℕ) : ℕ∞) = ((b : ℕ) : ℕ∞) ↔ a = b := by norm_cast

-- Lt ℕ to ℤ: push_cast stops, norm_cast moves
example : True := by
  fail_if_success (have : ∀ (a b : ℕ), ((a : ℕ) : ℤ) < ((b : ℕ) : ℤ) ↔ a < b := by intro a b; push_cast; try rfl)
  trivial
example (a b : ℕ) : ((a : ℕ) : ℤ) < ((b : ℕ) : ℤ) ↔ a < b := by norm_cast

-- Lt ℕ to ℚ: push_cast stops, norm_cast moves
example : True := by
  fail_if_success (have : ∀ (a b : ℕ), ((a : ℕ) : ℚ) < ((b : ℕ) : ℚ) ↔ a < b := by intro a b; push_cast; try rfl)
  trivial
example (a b : ℕ) : ((a : ℕ) : ℚ) < ((b : ℕ) : ℚ) ↔ a < b := by norm_cast

-- Lt ℕ to ℝ: push_cast stops, norm_cast moves
example : True := by
  fail_if_success (have : ∀ (a b : ℕ), ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) ↔ a < b := by intro a b; push_cast; try rfl)
  trivial
example (a b : ℕ) : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) ↔ a < b := by norm_cast

-- Lt ℤ to ℚ: push_cast stops, norm_cast moves
example : True := by
  fail_if_success (have : ∀ (a b : ℤ), ((a : ℤ) : ℚ) < ((b : ℤ) : ℚ) ↔ a < b := by intro a b; push_cast; try rfl)
  trivial
example (a b : ℤ) : ((a : ℤ) : ℚ) < ((b : ℤ) : ℚ) ↔ a < b := by norm_cast

-- Lt ℤ to ℝ: push_cast stops, norm_cast moves
example : True := by
  fail_if_success (have : ∀ (a b : ℤ), ((a : ℤ) : ℝ) < ((b : ℤ) : ℝ) ↔ a < b := by intro a b; push_cast; try rfl)
  trivial
example (a b : ℤ) : ((a : ℤ) : ℝ) < ((b : ℤ) : ℝ) ↔ a < b := by norm_cast

-- Lt ℚ to ℝ: push_cast stops, norm_cast moves
example : True := by
  fail_if_success (have : ∀ (a b : ℚ), ((a : ℚ) : ℝ) < ((b : ℚ) : ℝ) ↔ a < b := by intro a b; push_cast; try rfl)
  trivial
example (a b : ℚ) : ((a : ℚ) : ℝ) < ((b : ℚ) : ℝ) ↔ a < b := by norm_cast

-- Lt ℕ to ℕ∞: push_cast stops, norm_cast moves
example : True := by
  fail_if_success (have : ∀ (a b : ℕ), ((a : ℕ) : ℕ∞) < ((b : ℕ) : ℕ∞) ↔ a < b := by intro a b; push_cast; try rfl)
  trivial
example (a b : ℕ) : ((a : ℕ) : ℕ∞) < ((b : ℕ) : ℕ∞) ↔ a < b := by norm_cast

-- Le ℕ to ℤ: push_cast stops, norm_cast moves
example : True := by
  fail_if_success (have : ∀ (a b : ℕ), ((a : ℕ) : ℤ) ≤ ((b : ℕ) : ℤ) ↔ a ≤ b := by intro a b; push_cast; try rfl)
  trivial
example (a b : ℕ) : ((a : ℕ) : ℤ) ≤ ((b : ℕ) : ℤ) ↔ a ≤ b := by norm_cast

-- Le ℕ to ℚ: push_cast stops, norm_cast moves
example : True := by
  fail_if_success (have : ∀ (a b : ℕ), ((a : ℕ) : ℚ) ≤ ((b : ℕ) : ℚ) ↔ a ≤ b := by intro a b; push_cast; try rfl)
  trivial
example (a b : ℕ) : ((a : ℕ) : ℚ) ≤ ((b : ℕ) : ℚ) ↔ a ≤ b := by norm_cast

-- Le ℕ to ℝ: push_cast stops, norm_cast moves
example : True := by
  fail_if_success (have : ∀ (a b : ℕ), ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) ↔ a ≤ b := by intro a b; push_cast; try rfl)
  trivial
example (a b : ℕ) : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) ↔ a ≤ b := by norm_cast

-- Le ℤ to ℚ: push_cast stops, norm_cast moves
example : True := by
  fail_if_success (have : ∀ (a b : ℤ), ((a : ℤ) : ℚ) ≤ ((b : ℤ) : ℚ) ↔ a ≤ b := by intro a b; push_cast; try rfl)
  trivial
example (a b : ℤ) : ((a : ℤ) : ℚ) ≤ ((b : ℤ) : ℚ) ↔ a ≤ b := by norm_cast

-- Le ℤ to ℝ: push_cast stops, norm_cast moves
example : True := by
  fail_if_success (have : ∀ (a b : ℤ), ((a : ℤ) : ℝ) ≤ ((b : ℤ) : ℝ) ↔ a ≤ b := by intro a b; push_cast; try rfl)
  trivial
example (a b : ℤ) : ((a : ℤ) : ℝ) ≤ ((b : ℤ) : ℝ) ↔ a ≤ b := by norm_cast

-- Le ℚ to ℝ: push_cast stops, norm_cast moves
example : True := by
  fail_if_success (have : ∀ (a b : ℚ), ((a : ℚ) : ℝ) ≤ ((b : ℚ) : ℝ) ↔ a ≤ b := by intro a b; push_cast; try rfl)
  trivial
example (a b : ℚ) : ((a : ℚ) : ℝ) ≤ ((b : ℚ) : ℝ) ↔ a ≤ b := by norm_cast

-- Le ℕ to ℕ∞: push_cast stops, norm_cast moves
example : True := by
  fail_if_success (have : ∀ (a b : ℕ), ((a : ℕ) : ℕ∞) ≤ ((b : ℕ) : ℕ∞) ↔ a ≤ b := by intro a b; push_cast; try rfl)
  trivial
example (a b : ℕ) : ((a : ℕ) : ℕ∞) ≤ ((b : ℕ) : ℕ∞) ↔ a ≤ b := by norm_cast

-- Prod ℕ to ℤ: push_cast moves, norm_cast moves
example (s : Finset ℕ) (f : ℕ → ℕ) : ((∏ i ∈ s, f i : ℕ) : ℤ) = ∏ i ∈ s, (f i : ℤ) := by push_cast; try rfl
example (s : Finset ℕ) (f : ℕ → ℕ) : ((∏ i ∈ s, f i : ℕ) : ℤ) = ∏ i ∈ s, (f i : ℤ) := by norm_cast

-- Prod ℕ to ℚ: push_cast moves, norm_cast moves
example (s : Finset ℕ) (f : ℕ → ℕ) : ((∏ i ∈ s, f i : ℕ) : ℚ) = ∏ i ∈ s, (f i : ℚ) := by push_cast; try rfl
example (s : Finset ℕ) (f : ℕ → ℕ) : ((∏ i ∈ s, f i : ℕ) : ℚ) = ∏ i ∈ s, (f i : ℚ) := by norm_cast

-- Prod ℕ to ℝ: push_cast moves, norm_cast moves
example (s : Finset ℕ) (f : ℕ → ℕ) : ((∏ i ∈ s, f i : ℕ) : ℝ) = ∏ i ∈ s, (f i : ℝ) := by push_cast; try rfl
example (s : Finset ℕ) (f : ℕ → ℕ) : ((∏ i ∈ s, f i : ℕ) : ℝ) = ∏ i ∈ s, (f i : ℝ) := by norm_cast

-- Prod ℕ to ℂ: push_cast moves, norm_cast moves
example (s : Finset ℕ) (f : ℕ → ℕ) : ((∏ i ∈ s, f i : ℕ) : ℂ) = ∏ i ∈ s, (f i : ℂ) := by push_cast; try rfl
example (s : Finset ℕ) (f : ℕ → ℕ) : ((∏ i ∈ s, f i : ℕ) : ℂ) = ∏ i ∈ s, (f i : ℂ) := by norm_cast

-- Prod ℤ to ℚ: push_cast moves, norm_cast moves
example (s : Finset ℕ) (f : ℕ → ℤ) : ((∏ i ∈ s, f i : ℤ) : ℚ) = ∏ i ∈ s, (f i : ℚ) := by push_cast; try rfl
example (s : Finset ℕ) (f : ℕ → ℤ) : ((∏ i ∈ s, f i : ℤ) : ℚ) = ∏ i ∈ s, (f i : ℚ) := by norm_cast

-- Prod ℤ to ℝ: push_cast moves, norm_cast moves
example (s : Finset ℕ) (f : ℕ → ℤ) : ((∏ i ∈ s, f i : ℤ) : ℝ) = ∏ i ∈ s, (f i : ℝ) := by push_cast; try rfl
example (s : Finset ℕ) (f : ℕ → ℤ) : ((∏ i ∈ s, f i : ℤ) : ℝ) = ∏ i ∈ s, (f i : ℝ) := by norm_cast

-- Prod ℤ to ℂ: push_cast moves, norm_cast moves
example (s : Finset ℕ) (f : ℕ → ℤ) : ((∏ i ∈ s, f i : ℤ) : ℂ) = ∏ i ∈ s, (f i : ℂ) := by push_cast; try rfl
example (s : Finset ℕ) (f : ℕ → ℤ) : ((∏ i ∈ s, f i : ℤ) : ℂ) = ∏ i ∈ s, (f i : ℂ) := by norm_cast

-- Prod ℚ to ℝ: push_cast moves, norm_cast moves
example (s : Finset ℕ) (f : ℕ → ℚ) : ((∏ i ∈ s, f i : ℚ) : ℝ) = ∏ i ∈ s, (f i : ℝ) := by push_cast; try rfl
example (s : Finset ℕ) (f : ℕ → ℚ) : ((∏ i ∈ s, f i : ℚ) : ℝ) = ∏ i ∈ s, (f i : ℝ) := by norm_cast

-- Prod ℚ to ℂ: push_cast moves, norm_cast moves
example (s : Finset ℕ) (f : ℕ → ℚ) : ((∏ i ∈ s, f i : ℚ) : ℂ) = ∏ i ∈ s, (f i : ℂ) := by push_cast; try rfl
example (s : Finset ℕ) (f : ℕ → ℚ) : ((∏ i ∈ s, f i : ℚ) : ℂ) = ∏ i ∈ s, (f i : ℂ) := by norm_cast

-- Prod ℝ to ℂ: push_cast moves, norm_cast moves
example (s : Finset ℕ) (f : ℕ → ℝ) : ((∏ i ∈ s, f i : ℝ) : ℂ) = ∏ i ∈ s, (f i : ℂ) := by push_cast; try rfl
example (s : Finset ℕ) (f : ℕ → ℝ) : ((∏ i ∈ s, f i : ℝ) : ℂ) = ∏ i ∈ s, (f i : ℂ) := by norm_cast

end Parley.Tests.CastTable
