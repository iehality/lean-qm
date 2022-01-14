import order.bounded_lattice

universes u v

@[notation_class] class has_orthocompl (α : Type*) := (orthocompl : α → α)
postfix `′`:(max+1) := has_orthocompl.orthocompl

class ortholattice (α : Type u) extends bounded_lattice α, has_orthocompl α :=
(double_compl : ∀ x : α, x′′ = x)
(contraposition : ∀ x y : α, x ≤ y → y′ ≤ x′)
(inf_compl_le_bot : ∀ x : α, x ⊓ x′ ≤ ⊥)

class orthomodular_lattice (α : Type u) extends ortholattice α :=
(orthomodularity : ∀ x y : α, x ⊓ (x′ ⊔ (x ⊓ y)) ≤ y)


