import Game.Levels.SubgroupWorld.L02_mem_in_subg

World "SubgroupWorld"
Level 3
Title "Membership of inverses in a subgroup generated from a subset"

namespace MyGroup

/-- if a current assumption matches the goal, it is applied-/
TacticDoc assumption

NewTactic assumption

Introduction "TBA"

Statement {G : Type _} [Group G] (S : MySet G) (a : G) (ha : a ∈ S) :
  Generated_Subgroup S a⁻¹ := by
    have ha_mem := by apply Generated_Subgroup.base ha
    apply Generated_Subgroup.inv
    assumption

Conclusion "TBA"
