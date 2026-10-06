import Game.Levels.GroupWorld.L01_one_id

World "GroupWorld"
Level 2
Title "Unique Inverses"

namespace MyGroup

Introduction "TBA"

/-- Let $g$, $h$, and $h'$ be elements of a group $G$. If $h * g = g * h′ =$ the group identity, then $h = h′$.-/
Statement {G : Type _} [Group G] (g h h' : G) : h * g = Identity.id ∧ g * h'
  = Identity.id → h = h' := by
    intro hyp
    cases hyp with
    | intro hyp_hg hyp_gh' =>
      have p_mult : (h * g) * h' = Identity.id * h' := by rw [hyp_hg]
      rwa [Semigroup.mul_assoc, hyp_gh', Monoid.mul_id, Monoid.id_mul] at p_mult

Conclusion "TBA"
