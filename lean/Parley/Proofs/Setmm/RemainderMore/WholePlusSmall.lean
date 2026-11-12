module

public import AlgebraTactics
public import InstanceTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall
public import Parley.Proofs.Setmm.RemainderFacts.RemainderShifts

/-! Written from proofs/setmm/remainder-more.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.RemainderMore.WholePlusSmall

theorem whole_plus_small (A : ℤ) (hH1 : 0 ≤ A) (M : ℤ) (hH2 : 0 < M) (hH3 : A < M) :
    (M + A) % M = A := by
  -- 1. algebra
  have s1 : M + A = A + M := by parley_ring
  -- 2. calculation
  calc (M + A) % M = (A + M) % M := by (have h := congrArg (fun t : ℤ => t % M) s1; push_cast at h ⊢; all_goals exact_mod_cast h)
    _ = A % M := by
        have hI : (A + M * 1) % M = A % M := by parley_instance_cast ((Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (A : ℝ)) (M := (M : ℝ)) (by exact_mod_cast hH2) (K := (1 : ℤ))))
        simpa only [mul_one] using hI
    _ = A := by
        have hI : A % M = A := by parley_instance_cast ((Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := (A : ℝ)) (B := (M : ℝ)) (by exact_mod_cast hH2) (by exact_mod_cast ge_iff_le.mp hH1) (by exact_mod_cast hH3)))
        exact hI

end Parley.Proofs.Setmm.RemainderMore.WholePlusSmall
