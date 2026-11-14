module

public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Lean.Parser.Command
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Bounds of a logarithm of a whole number

The bounds real arithmetic takes ln p between (`reals::ln_bracket`): from
2 < e < 3, a power of 3 at most a power of p puts ln p above a fraction,
and a power of p at most a power of 2 puts it below one.
-/

public section

namespace LeanBridges.Logarithms

/-- ln p above a/b where 3ᵃ ≤ pᵇ: eᵃ < 3ᵃ ≤ pᵇ, as e < 3. -/
theorem log_above {p a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h : 3 ^ a ≤ p ^ b) :
    (a : ℝ) / b < Real.log p := by
  have hpb : (3 : ℝ) ^ a ≤ (p : ℝ) ^ b := by exact_mod_cast h
  rw [div_lt_iff₀ (by exact_mod_cast hb), mul_comm, ← Real.log_pow]
  calc (a : ℝ) = Real.log (Real.exp 1 ^ a) := by rw [Real.log_pow, Real.log_exp]; ring
    _ < Real.log ((p : ℝ) ^ b) :=
      Real.log_lt_log (by positivity)
        (lt_of_lt_of_le (pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos 1).le ha.ne') hpb)

/-- ln p below a/b where pᵇ ≤ 2ᵃ: pᵇ ≤ 2ᵃ < eᵃ, as 2 < e. -/
theorem log_below {p a b : ℕ} (hp : 0 < p) (ha : 0 < a) (hb : 0 < b) (h : p ^ b ≤ 2 ^ a) :
    Real.log p < (a : ℝ) / b := by
  have hpb : (p : ℝ) ^ b ≤ (2 : ℝ) ^ a := by exact_mod_cast h
  rw [lt_div_iff₀ (by exact_mod_cast hb), mul_comm, ← Real.log_pow]
  calc Real.log ((p : ℝ) ^ b) < Real.log (Real.exp 1 ^ a) :=
        Real.log_lt_log (by positivity)
          (lt_of_le_of_lt hpb (pow_lt_pow_left₀ Real.exp_one_gt_two (by norm_num) ha.ne'))
    _ = a := by rw [Real.log_pow, Real.log_exp]; ring

end LeanBridges.Logarithms
