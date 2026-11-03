module

public import Tactics
public import Parley.Tests.Elaborator.RecursionShapesCited.TwoSequences

/-! Written from tests/elaborator/recursion-shapes-cited.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RecursionShapesCited.TwoSequencesAgain

theorem two_sequences_again (F : ℤ → ℤ) (G : ℤ → ℤ) (hD1 : F 0 = (0 : ℤ) ∧ G 0 = (1 : ℤ) ∧ ∀ n : ℤ, 0 ≤ n → F (n + 1) = G n ∧ G (n + 1) = F n + G n) :
    F 1 = 1 := by
  -- 1. thm:two-sequences
  have s1 : F 1 = 1 := by first | linear_combination (norm := parley_norm) (Parley.Tests.Elaborator.RecursionShapesCited.TwoSequences.two_sequences (F := F) (G := G) (by parley_side)) | (have h := (Parley.Tests.Elaborator.RecursionShapesCited.TwoSequences.two_sequences (F := F) (G := G) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Tests.Elaborator.RecursionShapesCited.TwoSequences.two_sequences (F := F) (G := G) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Tests.Elaborator.RecursionShapesCited.TwoSequences.two_sequences (F := F) (G := G) (by parley_side)) | exact_mod_cast ((Parley.Tests.Elaborator.RecursionShapesCited.TwoSequences.two_sequences (F := F) (G := G) (by parley_side))).symm | (have h := (Parley.Tests.Elaborator.RecursionShapesCited.TwoSequences.two_sequences (F := F) (G := G) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Tests.Elaborator.RecursionShapesCited.TwoSequences.two_sequences (F := F) (G := G) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Tests.Elaborator.RecursionShapesCited.TwoSequences.two_sequences (F := F) (G := G) (by parley_side)); parley_int_power h) | (have h := (Parley.Tests.Elaborator.RecursionShapesCited.TwoSequences.two_sequences (F := F) (G := G) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.RecursionShapesCited.TwoSequencesAgain
