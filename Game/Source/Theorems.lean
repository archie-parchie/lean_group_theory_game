-- A file containing all of my original definitions and theorems

set_option autoImplicit true

-- creating a semigroup typeclass which extends the inbuilt Mul typeclass
class Semigroup (G : Type _) extends Mul G where
  mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c)

-- creating a custom identity typeclass
class Identity (G : Type _) where
  id : G

-- creating a monoid typeclass which extends the semigroup typeclass with the monoid typeclass
class Monoid (G : Type _) extends Semigroup G, Identity G where
  id_mul : ∀ a : G, Identity.id * a = a
  mul_id : ∀ a : G, a * Identity.id = a

-- creating a group typeclass which extends the monoid typeclass by introducing inverses
class Group (G : Type _) extends Monoid G, Inv G where
  left_inv : ∀ a : G, a⁻¹ * a = Identity.id

/-lemma 21.3: a) Suppose that g ∈ G has the following property: for every h in G,
 - we have g · h = h · g = h. Then g = e_G. -/
theorem one_id {G : Type _} [Group G] (g h : G) : g * h = h ∧ h * g = h → g = Identity.id := by
  intro hyp;
  cases hyp with
  | intro hyp_gh hyp_hg =>
    have hyp_mult : h⁻¹ * (h * g) = h⁻¹ * h := by rw [hyp_hg]
    rwa [← Semigroup.mul_assoc, Group.left_inv, Monoid.id_mul] at hyp_mult

/-lemma 21.3: b) Suppose that g ∈ G is an element. Suppose that h and h′ are also
elements of G, so that h · g = g · h′ = e_G. Then h = h′. -/
theorem unique_inv {G : Type _} [Group G] (g h h' : G) : h * g = Identity.id ∧ g * h'
  = Identity.id → h = h' := by
    intro hyp
    cases hyp with
    | intro hyp_hg hyp_gh' =>
      have p_mult : (h * g) * h' = Identity.id * h' := by rw [hyp_hg]
      rwa [Semigroup.mul_assoc, hyp_gh', Monoid.mul_id, Monoid.id_mul] at p_mult

-- creating an abelian group typeclass which extends the group typeclass by introducing commutative multiplication
class Ab_Group (α : Type _) extends Group α where
  mul_comm : ∀ a b : α, a * b = b * a

/- custom set declaration using the first few lines of the inbuilt mathlib set declaration -
 - see here: https://github.com/leanprover/lean4/blob/master/tests/elab/set.lean. This removes
 - any dependencies on libraries but is much less functional than a regular set.-/

abbrev MySet (α : Type u) := α → Prop

def MySet.in (s : MySet α) (a : α) := s a

notation:50 a " ∈ " s:50 => MySet.in s a

-- creating a subgroup typeclass which takes a set of elements of a group
class Subgroup {G : Type _} [Group G] (S : MySet G) : Prop where
  id_mem : Identity.id ∈ S
  inv_mem : ∀ a : G, a ∈ S → a⁻¹ ∈ S
  prod_mem : ∀ a b : G, a ∈ S ∧ b ∈ S → a * b ∈ S

-- defining an abelian subgroup as a subgroup which takes a set of elements of an abelian group
def Ab_Subgroup {G : Type _} [Ab_Group G] (S : MySet G) : Prop :=
  Subgroup S

/- lemma 22.10: Suppose that G is an abelian group. Suppose that H < G is a subgroup.
 - Then H is abelian. -/
theorem sub_of_ab_is_ab {G : Type _} [Ab_Group G] (S : MySet G) [Subgroup S] :
  ∀ a b : G, a ∈ S → b ∈ S → a * b = b * a := by
    intro x y ha hb
    exact Ab_Group.mul_comm x y

/- creating subgroups generated from a set as an inductive type - the type takes a set of elements from a group
 - and an element of that set, and repeatedly generates a subgroup -/
inductive Generated_Subgroup {G : Type _} [Group G] (S : MySet G) : G → Prop where
  | id : Generated_Subgroup S Identity.id
  | base {a : G} : a ∈ S → Generated_Subgroup S a
  | inv {a : G} : Generated_Subgroup S a → Generated_Subgroup S a⁻¹
  | prod {a b : G} : Generated_Subgroup S a → Generated_Subgroup S b →
      Generated_Subgroup S (a * b)

/- showing that a subgroup generated from a set is a subgroup by creating an instance of the subgroup typeclass-/
instance {G : Type _} [Group G] (S : MySet G) : Subgroup (Generated_Subgroup S) where
  id_mem := Generated_Subgroup.id
  inv_mem := by
    intro a ha
    apply Generated_Subgroup.inv ha
  prod_mem := by
    intro a b hab
    cases hab with
    | intro ha hb =>
      apply Generated_Subgroup.prod ha hb

-- if a in the subset, a in the subgroup generated
theorem mem_in_subg {G : Type _} [Group G] (S : MySet G) (a : G) (ha : a ∈ S) :
  Generated_Subgroup S a := by
    apply Generated_Subgroup.base ha

-- if a in the subset, a⁻¹ in the subgroup generated
theorem mem_inv_in_subg {G : Type _} [Group G] (S : MySet G) (a : G) (ha : a ∈ S) :
  Generated_Subgroup S a⁻¹ := by
    have ha_mem := by apply Generated_Subgroup.base ha
    apply Generated_Subgroup.inv
    assumption

-- if a in the subset, a * id in the generated subgroup
theorem mem_mul_id_in_subg {G : Type _} [Group G] (S : MySet G) (a : G) (ha : a ∈ S) :
  Generated_Subgroup S (a * Identity.id) := by
    have ha_mem := by apply Generated_Subgroup.base ha
    apply Generated_Subgroup.prod ha_mem Generated_Subgroup.id

-- if a, b in the subset, a * b in the generated subgroup
theorem mem_mul_mem_in_subg {G : Type _} [Group G] (S : MySet G) (a b : G) (ha : a ∈ S)
  (hb : b ∈ S) : Generated_Subgroup S (a * b) := by
    have ha_mem := by apply Generated_Subgroup.base ha
    have hb_mem := by apply Generated_Subgroup.base hb
    apply Generated_Subgroup.prod ha_mem hb_mem

-- if a, b in the subset, then a * b⁻¹ is in the generated subgroup
theorem mem_mul_meminv_in_subg {G : Type _} [Group G] (S : MySet G) (a b : G) (ha : a ∈ S)
  (hb : b ∈ S) : Generated_Subgroup S (a * b⁻¹) := by
    have ha_mem := by apply Generated_Subgroup.base ha
    have hb_mem := by apply Generated_Subgroup.base hb
    have hb_inv := by apply Generated_Subgroup.inv hb_mem
    apply Generated_Subgroup.prod ha_mem hb_inv

-- creating a group homomorphism typeclass which takes two groups of unknown types and a function between them
class Group_Hom {G : Type _} {H : Type _} [Group G] [Group H] (f : G → H) : Prop where
  hom_mul : ∀ g g' : G, f (g * g') = (f g) * (f g')

/-lemma 25.4: Suppose that ϕ: G → H is a homomorphism. Suppose that ψ : H → K is a homomorphism.
 - Then ψ ◦ ϕ: G → K is a homomorphism. -/
theorem hom_comp_hom_is_hom {G : Type _} {H : Type _} {K : Type _} [Group G] [Group H] [Group K]
  (φ : G → H) [Group_Hom φ] (ψ : H → K) [Group_Hom ψ] : Group_Hom (ψ ∘ φ) := by
    constructor
    intro hyp_g hyp_g'
    dsimp
    have hom1 : φ (hyp_g * hyp_g') = φ (hyp_g) * φ (hyp_g') := by apply Group_Hom.hom_mul
    have hom2 : ψ (φ (hyp_g) * φ (hyp_g')) = ψ (φ (hyp_g)) * ψ (φ (hyp_g')) := by apply Group_Hom.hom_mul
    rw [hom1, hom2]

-- under a homomorphism, the identity maps to the identity
theorem id_to_id_under_hom {G : Type _} {H : Type _} [Group G] [Group H] (φ : G → H) [Group_Hom φ]
  : φ Identity.id = Identity.id := by
    have idh : Identity.id * φ Identity.id = φ Identity.id  := by apply Monoid.id_mul
    symm
    have invh : ((φ Identity.id)⁻¹ * (φ Identity.id)) = Identity.id := by apply Group.left_inv
    rw [←invh, Semigroup.mul_assoc] at idh
    have homg : φ (Identity.id * Identity.id) = φ Identity.id * φ Identity.id :=
      by apply Group_Hom.hom_mul
    rw [←homg, Monoid.id_mul,Group.left_inv] at idh
    rw [idh]
