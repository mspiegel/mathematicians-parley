module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Groups
public import Parley.Proofs.Setmm.GroupCancellation.QuotientTimesDivisor
public import Parley.Proofs.Setmm.GroupCancellation.TheLeftIdentity

/-! Written from proofs/setmm/group-cancellation.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.GroupCancellation.QuotientIsIdentity

theorem quotient_is_identity {G : Type*} [Group G] (a : G) (hH2 : a ∈ (Set.univ : Set G)) (b : G) (hH3 : b ∈ (Set.univ : Set G)) :
    (a * b⁻¹ = (1 : G) ↔ a = b) := by
  -- the theorem. both directions
  have sThm : a * b⁻¹ = (1 : G) ↔ a = b := by
    constructor
    · skip
      intro hD1
      -- 1. thm:quotient-times-divisor, from H2, H3
      have s1 : a * b⁻¹ * b = a := by first | exact (Parley.Proofs.Setmm.GroupCancellation.QuotientTimesDivisor.quotient_times_divisor (G := G) (a := a) hH2 (b := b) hH3) | exact ((Parley.Proofs.Setmm.GroupCancellation.QuotientTimesDivisor.quotient_times_divisor (G := G) (a := a) hH2 (b := b) hH3)).symm | simpa using (Parley.Proofs.Setmm.GroupCancellation.QuotientTimesDivisor.quotient_times_divisor (G := G) (a := a) hH2 (b := b) hH3) | exact_mod_cast (Parley.Proofs.Setmm.GroupCancellation.QuotientTimesDivisor.quotient_times_divisor (G := G) (a := a) hH2 (b := b) hH3) | (have h := (Parley.Proofs.Setmm.GroupCancellation.QuotientTimesDivisor.quotient_times_divisor (G := G) (a := a) hH2 (b := b) hH3); parley_set_side)
      -- 2. substitute a·b⁻¹ = e (D1) into line 1
      have s2 : (1 : G) * b = a := by parley_subst_at hD1 s1
      -- 3. calculation
      have s3 : a = b := by
        calc a = (1 : G) * b := by parley_set_side
          _ = b := by first | exact (Parley.Proofs.Setmm.GroupCancellation.TheLeftIdentity.the_left_identity (G := G) (a := b) hH3) | exact ((Parley.Proofs.Setmm.GroupCancellation.TheLeftIdentity.the_left_identity (G := G) (a := b) hH3)).symm | simpa using (Parley.Proofs.Setmm.GroupCancellation.TheLeftIdentity.the_left_identity (G := G) (a := b) hH3) | exact_mod_cast (Parley.Proofs.Setmm.GroupCancellation.TheLeftIdentity.the_left_identity (G := G) (a := b) hH3) | (have h := (Parley.Proofs.Setmm.GroupCancellation.TheLeftIdentity.the_left_identity (G := G) (a := b) hH3); parley_set_side)
      all_goals parley_set_side
    · skip
      intro hD2
      -- 4. calculation
      have s4 : a * b⁻¹ = (1 : G) := by
        calc a * b⁻¹ = b * b⁻¹ := by parley_subst hD2
          _ = (1 : G) := by first | exact (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := b) hH3) | exact ((Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := b) hH3)).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := b) hH3) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := b) hH3) | (have h := (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := b) hH3); parley_set_side)
      all_goals parley_set_side
  all_goals parley_set_side

end Parley.Proofs.Setmm.GroupCancellation.QuotientIsIdentity
