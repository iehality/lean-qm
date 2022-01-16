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

attribute [simp] double_compl

@[simp] lemma inf_compl_eq_bot (a : α) : a ⊓ a′ = ⊥ := antisymm (inf_compl_le_bot a) (by simp)

@[simp] lemma sup_compl_eq_top (a : α) : a ⊔ a′ = ⊤ := antisymm (by simp) (top_le_sup_compl a)

@[simp] lemma inf_compl_eq_bot' (a : α) : a′ ⊓ a = ⊥ := by simp[@inf_comm _ _ a′ a]

@[simp] lemma sup_compl_eq_top' (a : α) : a′ ⊔ a = ⊤ := by simp[@sup_comm _ _ a′ a]

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
(orthomodularity : ∀ x y : α, x ⊔ (x′ ⊓ (x ⊔ y)) = x ⊔ y)

namespace orthomodular_lattice
variables {α : Type u} [orthomodular_lattice α]
open ortholattice

attribute [simp] orthomodularity

def commutes (a b : α) : Prop := a = (a ⊓ b) ⊔ (a ⊓ b′)

infix ` ⫰ `:50 := commutes

lemma commutes_of_le {a b : α} (h : a ≤ (a ⊓ b) ⊔ (a ⊓ b′)) : a ⫰ b := antisymm h (by simp)

lemma commutes.eql {a b : α} (h : a ⫰ b) : (a ⊓ b) ⊔ (a ⊓ b′) = a := eq.symm h

@[refl, simp] lemma commutes.refl (a : α) : a ⫰ a := by simp[commutes]

lemma commutes.complr {a b : α} : a ⫰ b → a ⫰ b′ :=
λ h, by {simp[commutes, @sup_comm _ _ (a ⊓ b′)], exact h }

@[simp] lemma commutes.complr_iff {a b : α} : a ⫰ b′ ↔ a ⫰ b:=
⟨λ h, by { have := h.complr, simp at this, exact this }, λ h, h.complr⟩

lemma orthomodularity' {a b : α} : a ≤ b → a ⊔ (a′ ⊓ b) = b := λ h,
have a ⊔ b = b, from sup_eq_right.mpr h,
calc a ⊔ (a′ ⊓ b) = a ⊔ (a′ ⊓ (a ⊔ b)) : by simp[this]
              ... = a ⊔ b              : orthomodularity a b
              ... = b                  : by simp[this]

lemma orthomodularity'' {a b : α} : a ≤ b → a′ ⊓ b = ⊥ → a = b := λ le h,
by { have := orthomodularity' le, simp[h] at this, exact this }

@[symm] lemma commutes.symm {α} [orthomodular_lattice α] {a b : α} : a ⫰ b → b ⫰ a := λ h,
begin
  have : a′ ⊓ b = (a ⊓ b)′ ⊓ b,
    calc a′ ⊓ b = ((a ⊓ b) ⊔ (a ⊓ b′))′ ⊓ b : by simp[h.eql]
            ... = (a′ ⊔ b′) ⊓ (a′ ⊔ b) ⊓ b  : by simp[sup_compl, inf_compl]
            ... = (a ⊓ b)′ ⊓ b              : by simp[inf_compl, inf_assoc, show (a′ ⊔ b) ⊓ b = b, by simp],
  calc b = a ⊓ b ⊔ (a ⊓ b)′ ⊓ b : by symmetry; from orthomodularity' (by simp)
     ... = a ⊓ b ⊔ a′ ⊓ b       : by simp[this]
     ... = b ⊓ a ⊔ b ⊓ a′       : by simp[@inf_comm _ _ b a, @inf_comm _ _ b a′]
end

lemma commutes.compll {α} [orthomodular_lattice α] {a b : α} : a ⫰ b → a′ ⫰ b :=
λ h, h.symm.complr.symm

lemma commutes.sup_inf {a b : α} (c : a ⫰ b) : (a ⊔ b) ⊓ (a ⊔ b′) = a :=
begin
  have := congr_arg has_orthocompl.orthocompl c.compll.complr,
  simp[inf_compl, sup_compl] at this, exact this.symm
end

lemma commutes.inf_compl_sup {a b : α} (c : a ⫰ b) :
  a ⊓ (a′ ⊔ b) = a ⊓ b :=
calc a ⊓ (a′ ⊔ b) = a ⊓ (b ⊔ a) ⊓ (b ⊔ a′) : by simp[show a ⊓ (b ⊔ a) = a, by simp, @sup_comm _ _ a′ b]
              ... = a ⊓ b                  : by simp[inf_assoc, c.symm.sup_inf]

theorem Foulis_Holland₁ {a b c : α} (c₁ : a ⫰ b) (c₂ : a ⫰ c) :
  (a ⊓ b) ⊔ (a ⊓ c) = a ⊓ (b ⊔ c) :=
begin
  suffices : ((a ⊓ b) ⊔ (a ⊓ c))′ ⊓ (a ⊓ (b ⊔ c)) = ⊥, from orthomodularity'' le_inf_sup this,
  have : a ⊓ (a′ ⊔ b′) ⊓ (a′ ⊔ c′) = a ⊓ b′ ⊓ c′,
    calc a ⊓ (a′ ⊔ b′) ⊓ (a′ ⊔ c′) = a ⊓ b′ ⊓ (a′ ⊔ c′)   : by simp[c₁.complr.inf_compl_sup]
                               ... = b′ ⊓ (a ⊓ (a′ ⊔ c′)) : by simp[@inf_comm _ _ b′, inf_assoc]
                               ... = b′ ⊓ (a ⊓ c′)        : by simp[c₂.complr.inf_compl_sup]
                               ... = a ⊓ b′ ⊓ c′          : by simp[@inf_comm _ _ b′, ←inf_assoc],
  calc
    (a ⊓ b ⊔ a ⊓ c)′ ⊓ (a ⊓ (b ⊔ c))
      = (a′ ⊔ b′) ⊓ (a′ ⊔ c′) ⊓ a ⊓ (b ⊔ c) : by simp[sup_compl, inf_compl, inf_assoc]
  ... = a ⊓ (a′ ⊔ b′) ⊓ (a′ ⊔ c′) ⊓ (b ⊔ c) : by simp[@inf_comm _ _ _ a, ←inf_assoc]
  ... = a ⊓ b′ ⊓ c′ ⊓ (b ⊔ c)               : by simp[this]
  ... = a ⊓ (b ⊔ c)′ ⊓ (b ⊔ c)              : by simp[show a ⊓ b′ ⊓ c′ = a ⊓ (b ⊔ c)′, by simp[sup_compl, inf_assoc]]
  ... = ⊥                                   : by simp[inf_assoc]
end

end orthomodular_lattice

