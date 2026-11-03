module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Groups
public import Parley.Proofs.Setmm.GroupCancellation.TheLeftIdentity
public import Parley.Proofs.Setmm.GroupCancellation.TheLeftInverse

/-! Written from proofs/setmm/group-cancellation.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.GroupCancellation.LeftCancellation

theorem left_cancellation {G : Type*} [Group G] (a : G) (hH2 : a ∈ (Set.univ : Set G)) (b : G) (hH3 : b ∈ (Set.univ : Set G)) (g : G) (hH4 : g ∈ (Set.univ : Set G)) :
    (g * a = g * b ↔ a = b) := by
  -- the theorem. both directions
  have sThm : g * a = g * b ↔ a = b := by
    constructor
    · skip
      intro hD1
      -- 1. axi:group-inverse-closed a := g, from H4
      have s1 : g⁻¹ ∈ (Set.univ : Set G) := by first | exact (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := g) hH4) | exact ((Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := g) hH4)).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := g) hH4) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := g) hH4) | (have h := (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := g) hH4); parley_set_side)
      -- 2. thm:the-left-inverse a := g, from H4
      have s2 : g⁻¹ * g = (1 : G) := by first | exact (Parley.Proofs.Setmm.GroupCancellation.TheLeftInverse.the_left_inverse (G := G) (a := g) hH4) | exact ((Parley.Proofs.Setmm.GroupCancellation.TheLeftInverse.the_left_inverse (G := G) (a := g) hH4)).symm | simpa using (Parley.Proofs.Setmm.GroupCancellation.TheLeftInverse.the_left_inverse (G := G) (a := g) hH4) | exact_mod_cast (Parley.Proofs.Setmm.GroupCancellation.TheLeftInverse.the_left_inverse (G := G) (a := g) hH4) | (have h := (Parley.Proofs.Setmm.GroupCancellation.TheLeftInverse.the_left_inverse (G := G) (a := g) hH4); parley_set_side)
      -- 3. axi:group-associative a := g⁻¹, b := g, c := a, from H2, H4, 1
      have s3 : g⁻¹ * g * a = g⁻¹ * (g * a) := by first | exact (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := g⁻¹) (b := g) (c := a) s1 hH4 hH2) | exact ((Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := g⁻¹) (b := g) (c := a) s1 hH4 hH2)).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := g⁻¹) (b := g) (c := a) s1 hH4 hH2) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := g⁻¹) (b := g) (c := a) s1 hH4 hH2) | (have h := (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := g⁻¹) (b := g) (c := a) s1 hH4 hH2); parley_set_side)
      -- 4. axi:group-associative a := g⁻¹, b := g, c := b, from H3, H4, 1
      have s4 : g⁻¹ * g * b = g⁻¹ * (g * b) := by first | exact (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := g⁻¹) (b := g) (c := b) s1 hH4 hH3) | exact ((Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := g⁻¹) (b := g) (c := b) s1 hH4 hH3)).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := g⁻¹) (b := g) (c := b) s1 hH4 hH3) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := g⁻¹) (b := g) (c := b) s1 hH4 hH3) | (have h := (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := g⁻¹) (b := g) (c := b) s1 hH4 hH3); parley_set_side)
      -- 5. substitute g⁻¹·g = e (line 2) into line 3
      have s5 : (1 : G) * a = g⁻¹ * (g * a) := by parley_subst_at s2 s3
      -- 6. substitute g·a = g·b (D1) into line 5
      have s6 : (1 : G) * a = g⁻¹ * (g * b) := by parley_subst_at hD1 s5
      -- 7. substitute g⁻¹·g = e (line 2) into line 4
      have s7 : (1 : G) * b = g⁻¹ * (g * b) := by parley_subst_at s2 s4
      -- 8. calculation
      have s8 : a = b := by
        calc a = (1 : G) * a := by first | exact (Parley.Proofs.Setmm.GroupCancellation.TheLeftIdentity.the_left_identity (G := G) (a := a) hH2) | exact ((Parley.Proofs.Setmm.GroupCancellation.TheLeftIdentity.the_left_identity (G := G) (a := a) hH2)).symm | simpa using (Parley.Proofs.Setmm.GroupCancellation.TheLeftIdentity.the_left_identity (G := G) (a := a) hH2) | exact_mod_cast (Parley.Proofs.Setmm.GroupCancellation.TheLeftIdentity.the_left_identity (G := G) (a := a) hH2) | (have h := (Parley.Proofs.Setmm.GroupCancellation.TheLeftIdentity.the_left_identity (G := G) (a := a) hH2); parley_set_side)
          _ = g⁻¹ * (g * b) := by parley_set_side
          _ = (1 : G) * b := by parley_set_side
          _ = b := by first | exact (Parley.Proofs.Setmm.GroupCancellation.TheLeftIdentity.the_left_identity (G := G) (a := b) hH3) | exact ((Parley.Proofs.Setmm.GroupCancellation.TheLeftIdentity.the_left_identity (G := G) (a := b) hH3)).symm | simpa using (Parley.Proofs.Setmm.GroupCancellation.TheLeftIdentity.the_left_identity (G := G) (a := b) hH3) | exact_mod_cast (Parley.Proofs.Setmm.GroupCancellation.TheLeftIdentity.the_left_identity (G := G) (a := b) hH3) | (have h := (Parley.Proofs.Setmm.GroupCancellation.TheLeftIdentity.the_left_identity (G := G) (a := b) hH3); parley_set_side)
      all_goals parley_set_side
    · skip
      intro hD2
      -- 9. substitute a = b (D2)
      have s9 : g * a = g * b := by parley_subst hD2
      all_goals parley_set_side
  all_goals parley_set_side

end Parley.Proofs.Setmm.GroupCancellation.LeftCancellation
