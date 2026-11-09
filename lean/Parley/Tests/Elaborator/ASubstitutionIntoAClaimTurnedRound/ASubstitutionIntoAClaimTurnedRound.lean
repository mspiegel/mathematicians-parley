module

public import SetTactics
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

namespace Parley.Tests.Elaborator.ASubstitutionIntoAClaimTurnedRound.ASubstitutionIntoAClaimTurnedRound

theorem a_substitution_into_a_claim_turned_round (G : ℤ → ℤ) (hH1 : Set.MapsTo G {n : ℤ | 0 ≤ n} {n : ℤ | 0 < n}) (hH2 : G 0 = 1) :
    0 + 1 = 0 + G 0 := by
  -- 1. substitute G(0) = 1 (H2)
  (have h := congrArg (fun t : ℤ => 0 + t) (hH2).symm; push_cast at h ⊢; all_goals exact_mod_cast h)

end Parley.Tests.Elaborator.ASubstitutionIntoAClaimTurnedRound.ASubstitutionIntoAClaimTurnedRound
