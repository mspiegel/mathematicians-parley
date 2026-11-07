module

public import SetTactics
public import SubstTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/a-substitution-into-a-claim-turned-round.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ASubstitutionIntoAClaimTurnedRound.ASubstitutionIntoAClaim

theorem a_substitution_into_a_claim (G : ℤ → ℤ) (hH1 : Set.MapsTo G {n : ℤ | 0 ≤ n} {n : ℤ | 0 < n}) (hH2 : G 0 = 1) :
    0 + G 0 = 0 + 1 := by
  -- 1. substitute G(0) = 1 (H2)
  have s1 : 0 + G 0 = 0 + 1 := by parley_subst hH2
  all_goals exact s1

end Parley.Tests.Elaborator.ASubstitutionIntoAClaimTurnedRound.ASubstitutionIntoAClaim
