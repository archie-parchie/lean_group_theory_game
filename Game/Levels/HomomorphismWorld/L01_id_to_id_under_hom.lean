import Game.Levels.SubgroupWorld

World "HomomorphismWorld"
Level 1
Title "A homomorphism sends the identity to the identity"

namespace MyGroup

/-- defining group homomorphisms-/
DefinitionDoc MyGroup.Group_Hom as "Group Homomorphism"

NewDefinition MyGroup.Group_Hom

/-- under a homomorphism, multiplication preserves the group structure-/
TheoremDoc MyGroup.Group_Hom.hom_mul as "Group_Hom.hom_mul"

NewTheorem MyGroup.Group_Hom.hom_mul

/-- reverses a symmetric relation-/
TacticDoc symm

NewTactic symm

Introduction "TBA"

/-- Let $G$ and $H$ be groups, and $φ : G → H$. Under $φ$, the identity in $G$ maps to the identity in $H$.-/
Statement {G : Type _} {H : Type _} [Group G] [Group H] (φ : G → H) [Group_Hom φ]
  : φ Identity.id = Identity.id := by
    have idh : Identity.id * φ Identity.id = φ Identity.id := by apply Monoid.id_mul
    symm
    have invh : ((φ Identity.id)⁻¹ * (φ Identity.id)) = Identity.id := by apply Group.left_inv
    rw [←invh, Semigroup.mul_assoc] at idh
    have homg : φ (Identity.id * Identity.id) = φ Identity.id * φ Identity.id :=
      by apply Group_Hom.hom_mul
    rw [←homg, Monoid.id_mul,Group.left_inv] at idh
    rw [idh]

Conclusion "TBA"
