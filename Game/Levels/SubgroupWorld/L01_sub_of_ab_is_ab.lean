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
