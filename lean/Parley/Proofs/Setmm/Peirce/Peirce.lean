module

public import Parley.Items.Stdlib.Reasoning
public import Parley.Library

/-! Written from proofs/setmm/peirce.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.Peirce.Peirce

theorem peirce (a : ℝ) (b : ℝ) :
    (((a = 0 → b = 0) → a = 0) → a = 0) := by
  -- the theorem. proof
  have sThm : ((a = 0 → b = 0) → a = 0) → a = 0 := by
    intro hK1
    by_contra hc_hS
    have hS : a ≠ 0 := by parley_suppose hc_hS
    -- 1. proof
    have s1 : a = 0 → b = 0 := by
      intro hK2
      -- 1.1. restate S
      have s1_1 : a ≠ 0 := by parley_side
      all_goals parley_side
    -- 2. mun:modus-ponens, from K1, 1
    have s2 : a = 0 := by linear_combination (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := a = 0 → b = 0) (Q := a = 0) (by parley_side) (by parley_side))
    all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.Peirce.Peirce
