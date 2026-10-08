import Game.Levels.HomomorphismWorld.L01_id_to_id_under_hom

World "HomomorphismWorld"
Level 2
Title "The composition of two homomorphisms is a homomorphism"

namespace MyGroup

/-- solves the goal with the first constructor that matches its type-/
TacticDoc constructor

/-- simplifies the goal with theorems that hold by reflexivity-/
TacticDoc dsimp

NewTactic constructor dsimp

Introduction "TBA"

/-- Let $G$, $H$ and $K$ be groups, and $φ$ and $ψ$ homomorphisms such that $φ : G → H$ and $ψ : H → G$. Then $ψ ∘ φ$ is a homomorphism from $G$ to $K$.-/
Statement {G : Type _} {H : Type _} {K : Type _} [Group G] [Group H] [Group K]
  (φ : G → H) [Group_Hom φ] (ψ : H → K) [Group_Hom ψ] : Group_Hom (ψ ∘ φ) := by
    constructor
    intro hyp_g hyp_g'
    dsimp
    have hom1 : φ (hyp_g * hyp_g') = φ (hyp_g) * φ (hyp_g') := by apply Group_Hom.hom_mul
    have hom2 : ψ (φ (hyp_g) * φ (hyp_g')) = ψ (φ (hyp_g)) * ψ (φ (hyp_g')) := by apply Group_Hom.hom_mul
    rw [hom1, hom2]

Conclusion "TBA"
