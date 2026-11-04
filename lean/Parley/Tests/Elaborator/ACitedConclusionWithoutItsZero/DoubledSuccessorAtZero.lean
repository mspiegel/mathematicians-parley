module

public import PowerTactics
public import Tactics
public import Parley.Tests.Elaborator.ACitedConclusionWithoutItsZero.DoubledSuccessor

/-! Written from tests/elaborator/a-cited-conclusion-without-its-zero.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ACitedConclusionWithoutItsZero.DoubledSuccessorAtZero

theorem doubled_successor_at_zero :
    (2 * 1 : ℤ) = 2 * 0 + 2 := by
  -- 1. thm:doubled-successor n := 0
  have s1 : (2 * 1 : ℤ) = 2 * 0 + 2 := by first | linear_combination (norm := parley_norm) (Parley.Tests.Elaborator.ACitedConclusionWithoutItsZero.DoubledSuccessor.doubled_successor (n := 0)) | (have h := (Parley.Tests.Elaborator.ACitedConclusionWithoutItsZero.DoubledSuccessor.doubled_successor (n := 0)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Tests.Elaborator.ACitedConclusionWithoutItsZero.DoubledSuccessor.doubled_successor (n := 0)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Tests.Elaborator.ACitedConclusionWithoutItsZero.DoubledSuccessor.doubled_successor (n := 0)) | exact_mod_cast ((Parley.Tests.Elaborator.ACitedConclusionWithoutItsZero.DoubledSuccessor.doubled_successor (n := 0))).symm | (have h := (Parley.Tests.Elaborator.ACitedConclusionWithoutItsZero.DoubledSuccessor.doubled_successor (n := 0)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Tests.Elaborator.ACitedConclusionWithoutItsZero.DoubledSuccessor.doubled_successor (n := 0)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Tests.Elaborator.ACitedConclusionWithoutItsZero.DoubledSuccessor.doubled_successor (n := 0)); parley_int_power h) | (have h := (Parley.Tests.Elaborator.ACitedConclusionWithoutItsZero.DoubledSuccessor.doubled_successor (n := 0)); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ACitedConclusionWithoutItsZero.DoubledSuccessorAtZero
