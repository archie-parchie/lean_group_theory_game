namespace MyGroup

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
