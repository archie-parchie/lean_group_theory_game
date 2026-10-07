import Game.Levels.GroupWorld

World "SubgroupWorld"
Level 1
Title "Subgroups of Abelian Groups"

namespace MyGroup

/-- defining abelian groups-/
DefinitionDoc MyGroup.Ab_Group as "Abelian Group"

/-- defining subgroups-/
DefinitionDoc MyGroup.Subgroup as "Subgroup"

/-- defining abelian subgroups-/
DefinitionDoc MyGroup.Ab_Subgroup as "Abelian Subgroup"

NewDefinition MyGroup.Ab_Group MyGroup.Subgroup MyGroup.Ab_Subgroup

/-- a proof that multiplication in an abelian group is commutative-/
TheoremDoc MyGroup.Ab_Group.mul_comm as "mul_comm"

/-- a proof that the identity is always in a subgroup-/
TheoremDoc MyGroup.Subgroup.id_mem as "id_mem"

/-- a proof that if a member is in a subgroup, so is its inverse-/
TheoremDoc MyGroup.Subgroup.inv_mem as "inv_mem"

/-- a proof that if two members are in the subgroup, so is its product-/
TheoremDoc MyGroup.Subgroup.prod_mem as "prod_mem"

NewTheorem MyGroup.Ab_Group.mul_comm MyGroup.Subgroup.id_mem MyGroup.Subgroup.inv_mem
  MyGroup.Subgroup.prod_mem

/-- closes the main goal if its type exactly matches-/
TacticDoc exact

NewTactic exact

Introduction "TBA"

/-- Let $G$ be an abelian group, and $H < G$ a subgroup. Then $H$ is abelian.-/
Statement {G : Type _} [Ab_Group G] (S : MySet G) [Subgroup S] :
  ∀ a b : G, a ∈ S → b ∈ S → a * b = b * a := by
    intro x y ha hb
    exact Ab_Group.mul_comm x y

Conclusion "TBA"
