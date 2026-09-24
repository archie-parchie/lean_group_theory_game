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
