import order.lattice
import order.complete_lattice
import order.bounded_order

universes u v

@[notation_class] class has_orthocompl (α : Type*) := (orthocompl : α → α)
postfix `′`:(max+1) := has_orthocompl.orthocompl

class ortholattice (α : Type u) extends lattice α, bounded_order α, has_orthocompl α :=
(double_compl : ∀ x : α, x′′ = x)
(contraposition : ∀ x y : α, x ≤ y → y′ ≤ x′)
(sup_compl : ∀ x y : α, (x ⊔ y)′ = x′ ⊓ y′)
(inf_compl_le_bot : ∀ x : α, x ⊓ x′ ≤ ⊥)
(top_le_sup_compl : ∀ x : α, ⊤ ≤ x ⊔ x′)

namespace ortholattice
variables {α : Type u} [ortholattice α]

@[simp] lemma compl_compl (a : α) : a′′ = a := double_compl a

@[simp] lemma inf_compl_eq_bot (a : α) : a ⊓ a′ = ⊥ := antisymm (inf_compl_le_bot a) (by simp)

@[simp] lemma sup_compl_eq_top (a : α) : a ⊔ a′ = ⊤ := antisymm (by simp) (top_le_sup_compl a)

lemma inf_compl (a b : α) : (a ⊓ b)′ = a′ ⊔ b′ :=
by { have : a ⊓ b = (a′ ⊔ b′)′, { simp[sup_compl] }, simp[this] }

@[simp] lemma top_compl : (⊤ : α)′ = ⊥ :=
by { rw [←inf_compl_eq_bot (⊤ : α)], simp[-inf_compl_eq_bot] }

@[simp] lemma bot_compl : (⊥ : α)′ = ⊤ :=
by { rw [←sup_compl_eq_top (⊥ : α)], simp[-sup_compl_eq_top] }

end ortholattice

class complete_ortholattice (α : Type u) extends complete_lattice α, has_orthocompl α :=
(double_compl : ∀ x : α, x′′ = x)
(contraposition : ∀ x y : α, x ≤ y → y′ ≤ x′)
(sup_compl : ∀ x y : α, (x ⊔ y)′ = x′ ⊓ y′)
(Sup_compl : ∀ s : set α, (has_Sup.Sup s)′ = ⨅ x ∈ s, x′)
(inf_compl_le_bot : ∀ x : α, x ⊓ x′ ≤ ⊥)
(top_le_sup_compl : ∀ x : α, ⊤ ≤ x ⊔ x′)

namespace complete_ortholattice
variables {α : Type u} [complete_ortholattice α]

instance : ortholattice α :=
{ double_compl := double_compl,
  contraposition := contraposition,
  sup_compl := sup_compl,
  inf_compl_le_bot := inf_compl_le_bot,
  top_le_sup_compl := top_le_sup_compl }

lemma supr_compl {ι} (f : ι → α) : (supr f)′ = ⨅ i, (f i)′ :=
by { show (Sup (set.range f))′ = ⨅ i, (f i)′,
     simp [Sup_compl (set.range f), show (⨅ x i (h : f i = x), x′) = (⨅ i x (h : f i = x), x′), from infi_comm] }

lemma Inf_compl (s : set α) : (Inf s)′ = ⨆ x ∈ s, x′ :=
by { have : Inf s = (⨆ x ∈ s, x′)′, { simp[supr_compl, Inf_eq_infi] }, simp[this] }

lemma infi_compl {ι} (f : ι → α) : (infi f)′ = ⨆ i, (f i)′ :=
by { show (Inf (set.range f))′ = ⨆ i, (f i)′,
     simp [Inf_compl (set.range f), show (⨆ x i (h : f i = x), x′) = (⨆ i x (h : f i = x), x′), from supr_comm] }

end complete_ortholattice

class orthomodular_lattice (α : Type u) extends ortholattice α :=
(orthomodularity : ∀ x y : α, x ⊓ (x′ ⊔ (x ⊓ y)) ≤ y)


