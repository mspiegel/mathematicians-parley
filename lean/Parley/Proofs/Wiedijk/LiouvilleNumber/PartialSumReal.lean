module

public import Counting
public import FactorialTactics
public import Tactics
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Wiedijk.LiouvilleNumber.TermsReal

/-! Written from proofs/wiedijk/liouville-number.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumReal

theorem partial_sum_real (m : ℕ) (hH1 : 0 < m) :
    True := by
  -- 1. D0, from H1
  have s1 : (∑ k ∈ Finset.Icc (1 : ℤ) (m : ℤ), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) = (∑ k ∈ Finset.Icc (1 : ℤ) (m : ℤ), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) := by parley_side
  -- 2. thm:terms-real
  -- 3. mun:sum-real a := 1, b := m, from 2
  -- 4. substitute Σ(k = 1 to m) 1/2^(k!) = s(m) (line 1) into line 3
  all_goals parley_side

end Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumReal
