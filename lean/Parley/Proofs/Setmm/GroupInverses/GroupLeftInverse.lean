module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Groups

/-! Written from proofs/setmm/group-inverses.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.GroupInverses.GroupLeftInverse

theorem group_left_inverse {G : Type*} [Group G] (a : G) (hH2 : a ∈ (Set.univ : Set G)) :
    a⁻¹ * a = (1 : G) := by
  -- 1. axi:group-identity-closed
  have s1 : (1 : G) ∈ (Set.univ : Set G) := by first | exact (Parley.Items.Stdlib.Groups.axi_group_identity_closed (G := G)) | exact ((Parley.Items.Stdlib.Groups.axi_group_identity_closed (G := G))).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_identity_closed (G := G)) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_identity_closed (G := G)) | (have h := (Parley.Items.Stdlib.Groups.axi_group_identity_closed (G := G)); parley_set_side)
  set b : G := a⁻¹ with hD1
  set c : G := b⁻¹ with hD2
  -- 2. axi:group-inverse-closed, from D1, H2
  have s2 : b ∈ (Set.univ : Set G) := by
    try simp only [hD1] at *
    try push_cast at *
    first | exact (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a) hH2) | exact ((Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a) hH2)).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a) hH2) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a) hH2) | (have h := (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := a) hH2); parley_set_side)
  -- 3. axi:group-inverse-closed a := b, from D2, 2
  have s3 : c ∈ (Set.univ : Set G) := by
    try simp only [hD2] at *
    try push_cast at *
    first | exact (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := b) s2) | exact ((Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := b) s2)).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := b) s2) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := b) s2) | (have h := (Parley.Items.Stdlib.Groups.axi_group_inverse_closed (G := G) (a := b) s2); parley_set_side)
  -- 4. axi:group-closed a := b, b := a, from H2, 2
  have s4 : b * a ∈ (Set.univ : Set G) := by first | exact (Parley.Items.Stdlib.Groups.axi_group_closed (G := G) (a := b) (b := a) s2 hH2) | exact ((Parley.Items.Stdlib.Groups.axi_group_closed (G := G) (a := b) (b := a) s2 hH2)).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_closed (G := G) (a := b) (b := a) s2 hH2) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_closed (G := G) (a := b) (b := a) s2 hH2) | (have h := (Parley.Items.Stdlib.Groups.axi_group_closed (G := G) (a := b) (b := a) s2 hH2); parley_set_side)
  -- 5. axi:group-closed a := b, b := c, from 2, 3
  have s5 : b * c ∈ (Set.univ : Set G) := by first | exact (Parley.Items.Stdlib.Groups.axi_group_closed (G := G) (a := b) (b := c) s2 s3) | exact ((Parley.Items.Stdlib.Groups.axi_group_closed (G := G) (a := b) (b := c) s2 s3)).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_closed (G := G) (a := b) (b := c) s2 s3) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_closed (G := G) (a := b) (b := c) s2 s3) | (have h := (Parley.Items.Stdlib.Groups.axi_group_closed (G := G) (a := b) (b := c) s2 s3); parley_set_side)
  -- 6. axi:group-inverse a := b, from D2, 2
  have s6 : b * c = (1 : G) := by
    try simp only [hD2] at *
    try push_cast at *
    first | exact (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := b) s2) | exact ((Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := b) s2)).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := b) s2) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := b) s2) | (have h := (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := b) s2); parley_set_side)
  -- 7. axi:group-inverse, from D1, H2
  have s7 : a * b = (1 : G) := by
    try simp only [hD1] at *
    try push_cast at *
    first | exact (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a) hH2) | exact ((Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a) hH2)).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a) hH2) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a) hH2) | (have h := (Parley.Items.Stdlib.Groups.axi_group_inverse (G := G) (a := a) hH2); parley_set_side)
  -- 8. calculation
  have s8 : a * (b * c) = (1 : G) * c := by
    calc a * (b * c) = a * b * c := by first | exact (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a) (b := b) (c := c) hH2 s2 s3) | exact ((Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a) (b := b) (c := c) hH2 s2 s3)).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a) (b := b) (c := c) hH2 s2 s3) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a) (b := b) (c := c) hH2 s2 s3) | (have h := (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := a) (b := b) (c := c) hH2 s2 s3); parley_set_side)
      _ = (1 : G) * c := by parley_subst s7
  -- 9. axi:group-identity a := b, from 2
  have s9 : b * (1 : G) = b := by first | exact (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := b) s2) | exact ((Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := b) s2)).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := b) s2) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := b) s2) | (have h := (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := b) s2); parley_set_side)
  -- 10. calculation
  have s10 : a⁻¹ * a = (1 : G) := by
    calc a⁻¹ * a = b * a := by first | (simp only [hD1]; push_cast; norm_num; done) | parley_set_side
      _ = b * a * (1 : G) := by first | exact (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := b * a) s4) | exact ((Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := b * a) s4)).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := b * a) s4) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := b * a) s4) | (have h := (Parley.Items.Stdlib.Groups.axi_group_identity (G := G) (a := b * a) s4); parley_set_side)
      _ = b * a * (b * c) := by parley_subst s6
      _ = b * (a * (b * c)) := by first | exact (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := b) (b := a) (c := b * c) s2 hH2 s5) | exact ((Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := b) (b := a) (c := b * c) s2 hH2 s5)).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := b) (b := a) (c := b * c) s2 hH2 s5) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := b) (b := a) (c := b * c) s2 hH2 s5) | (have h := (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := b) (b := a) (c := b * c) s2 hH2 s5); parley_set_side)
      _ = b * ((1 : G) * c) := by parley_subst s8
      _ = b * (1 : G) * c := by first | exact (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := b) (b := (1 : G)) (c := c) s2 s1 s3) | exact ((Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := b) (b := (1 : G)) (c := c) s2 s1 s3)).symm | simpa using (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := b) (b := (1 : G)) (c := c) s2 s1 s3) | exact_mod_cast (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := b) (b := (1 : G)) (c := c) s2 s1 s3) | (have h := (Parley.Items.Stdlib.Groups.axi_group_associative (G := G) (a := b) (b := (1 : G)) (c := c) s2 s1 s3); parley_set_side)
      _ = b * c := by parley_subst s9
      _ = (1 : G) := by parley_set_side
  all_goals exact s10

end Parley.Proofs.Setmm.GroupInverses.GroupLeftInverse
