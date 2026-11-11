module

public import SetTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Functions

/-! Written from tests/elaborator/a-pair-naming-a-define.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.APairNamingADefine.APairNamingADefine

theorem a_pair_naming_a_define {α : Type*} (X : Set α) (a : α) (hH3 : ∀ S ∈ 𝒫 X, ∀ T ∈ 𝒫 X, S ∪ ({a} : Set α) = T ∪ ({a} : Set α) → S = T) :
    (∃ g : Set α → Set α, Set.BijOn g (𝒫 X) ((fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 X))) := by
  set F : Set (Set α) := 𝒫 X with hD1
  -- 1. substitute F = 𝒫X (D1) into H3
  have s1 : ∀ S ∈ F, ∀ T ∈ F, S ∪ ({a} : Set α) = T ∪ ({a} : Set α) → S = T := by parley_subst_at hD1 hH3
  -- 2. mun:image-of-injection Y := F, from D1, 1
  try simp only [hD1] at ⊢
  try push_cast at ⊢
  exact (Parley.Items.Stdlib.Functions.mun_image_of_injection (Y := 𝒫 X) (a := a) s1)

end Parley.Tests.Elaborator.APairNamingADefine.APairNamingADefine
