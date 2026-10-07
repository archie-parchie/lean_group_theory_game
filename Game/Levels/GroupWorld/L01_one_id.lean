import GameServer
import Game.Source.Definitions

World "GroupWorld"
Level 1
Title "One Identity"

namespace MyGroup

/-- defining semigroups-/
DefinitionDoc MyGroup.Semigroup as "Semigroup"

/-- defining the identity-/
DefinitionDoc MyGroup.Identity as "Identity"

/-- defining monoids-/
DefinitionDoc MyGroup.Monoid as "Monoid"

/-- defining groups-/
DefinitionDoc MyGroup.Group as "Group"

NewDefinition MyGroup.Semigroup MyGroup.Identity MyGroup.Monoid
  MyGroup.Group

/-- a proof of multiplication being associative in a group-/
TheoremDoc MyGroup.Semigroup.mul_assoc as "mul_assoc"

/-- a proof of the existence of an identity element in a group-/
TheoremDoc MyGroup.Identity.id as "id"

/-- a proof that id * elem = elem-/
TheoremDoc MyGroup.Monoid.id_mul as "id_mul"

/-- a proof that elem * id = elem-/
TheoremDoc MyGroup.Monoid.mul_id as "mul_id"

/-- a proof that group elements have (left) inverses-/
TheoremDoc MyGroup.Group.left_inv as "leftinv"

NewTheorem MyGroup.Semigroup.mul_assoc MyGroup.Identity.id MyGroup.Monoid.id_mul
  MyGroup.Monoid.mul_id MyGroup.Group.left_inv

/-- intro stands for introduction-/
TacticDoc intro

/-- allows for different cases to be dealt with-/
TacticDoc cases

/-- rw stands for rewrite-/
TacticDoc rw

/-- rwa is a variant of rw-/
TacticDoc rwa

/-- creates an intermediate hypothesis-/
TacticDoc «have»

NewTactic intro cases rw «have»
NewHiddenTactic rwa

Introduction "TBA
This level can currently only be solved in code editor mode."

/-- Let $g$ and $h$ be elements of a group $G$. If $g * h = h$ and $h * g = h$, then $h$ is the group identity.-/
Statement {G : Type _} [Group G] (g h : G) : g * h = h ∧ h * g = h → g = Identity.id := by
  intro hyp;
  cases hyp with
  | intro hyp_gh hyp_hg =>
    have hyp_mult : h⁻¹ * (h * g) = h⁻¹ * h := by rw [hyp_hg]
    rwa [← Semigroup.mul_assoc, Group.left_inv, Monoid.id_mul] at hyp_mult

Conclusion "TBA"
