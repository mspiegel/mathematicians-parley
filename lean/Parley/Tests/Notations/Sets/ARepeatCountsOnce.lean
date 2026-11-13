module

public import ArithTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sets

/-! Written from tests/notations/sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Sets.ARepeatCountsOnce

theorem a_repeat_counts_once :
    (({(1 : ℤ), (2 : ℤ), (2 : ℤ)} : Set ℤ).ncard : ℤ) = 2 := by
  -- 1. mun:listed-repeat a := 1, b := 2
  have s1 : ({(1 : ℤ), (2 : ℤ), (2 : ℤ)} : Set ℤ) = ({(1 : ℤ), (2 : ℤ)} : Set ℤ) := by exact (Parley.Items.Stdlib.Sets.mun_listed_repeat (a := (1 : ℤ)) (b := (2 : ℤ)))
  -- 2. arithmetic
  have s2 : (1 : ℤ) ≠ 2 := by parley_arith
  -- 3. mun:card-pair-distinct u := 1, w := 2, from 2
  have s3 : (({(1 : ℤ), (2 : ℤ)} : Set ℤ).ncard : ℤ) = 2 := by exact ((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := (1 : ℤ)) (w := (2 : ℤ)))).mp (by (have h := s2; revert h; norm_num))
  -- 4. substitute {1, 2} = {1, 2, 2} (line 1) into line 3
  parley_subst_at s1 s3

end Parley.Tests.Notations.Sets.ARepeatCountsOnce
