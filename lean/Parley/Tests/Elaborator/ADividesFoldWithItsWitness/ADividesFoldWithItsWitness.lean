module

public import LeanBridges
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/a-divides-fold-with-its-witness.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ADividesFoldWithItsWitness.ADividesFoldWithItsWitness

theorem a_divides_fold_with_its_witness (m : ℝ) (m : ℕ) (hH2 : 0 < m) (hH3 : ∃ j : ℤ, ∃ k : ℤ, j ^ 2 + k ^ 2 = 3 * (m : ℤ) ^ 2) :
    (3 : ℤ) ∣ 3 * (m : ℤ) ^ 2 := by
  -- 1. obtain p, q from H3
  obtain ⟨p, q, s1⟩ := hH3
  -- 2. def:divides d := 3, n := p² + q², from H2, 1
  have s2 : (3 : ℤ) ∣ p ^ 2 + q ^ 2 := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := p ^ 2 + q ^ 2))).mpr ⟨(m : ℤ) ^ 2, by parley_side⟩
  -- 3. substitute p² + q² = 3m² (line 1) into line 2
  have s3 : (3 : ℤ) ∣ 3 * (m : ℤ) ^ 2 := by parley_subst_at s1 s2
  all_goals parley_side

end Parley.Tests.Elaborator.ADividesFoldWithItsWitness.ADividesFoldWithItsWitness
