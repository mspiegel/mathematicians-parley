module

public import Parley.Items.Stdlib.Numbers
public import Parley.Library

/-! Written from proofs/hammack/binet-formula.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.BinetFormula.PowerRecurrence

theorem power_recurrence (x : ℝ) (H2 : x ^ 2 = x + 1) (k : ℕ) :
    x ^ (k + 1 + 1) = x ^ (k + 1) + x ^ k := by
  -- 1. mun:exponent-step a := x, m := k
  have s1 : x ^ (k + 1) = x ^ k * x := by linear_combination (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := x) (m := k))
  -- 2. mun:exponent-step a := x, m := k + 1
  have s2 : x ^ (k + 1 + 1) = x ^ (k + 1) * x := by linear_combination (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := x) (m := k + 1))
  -- 3. calculation
  have s3 : x ^ (k + 1 + 1) = x ^ (k + 1) + x ^ k := by
    calc x ^ (k + 1 + 1) = x ^ k * x * x := by linear_combination (x) * s1 + s2
      _ = x ^ k * (x + 1) := by linear_combination (x ^ k) * H2
      _ = x ^ (k + 1) + x ^ k := by linear_combination (-1) * s1
  all_goals parley_side

end Parley.Proofs.Hammack.BinetFormula.PowerRecurrence
