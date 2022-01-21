import order.lattice
import order.complete_lattice
import order.bounded_order
import order.boolean_algebra
import data.set_like.basic

universes u v

@[notation_class] class has_orthocompl (α : Type*) := (orthocompl : α → α)
postfix `′`:(max+1) := has_orthocompl.orthocompl

class ortholattice (α : Type u) extends lattice α, bounded_order α, has_orthocompl α :=
(double_compl : ∀ x : α, x′′ = x)
(contraposition : ∀ x y : α, x ≤ y → y′ ≤ x′)
(sup_compl : ∀ x y : α, (x ⊔ y)′ = x′ ⊓ y′)
(inf_compl_le_bot : ∀ x : α, x ⊓ x′ ≤ ⊥)
(top_le_sup_compl : ∀ x : α, ⊤ ≤ x ⊔ x′)

class orthomodular_lattice (α : Type u) extends ortholattice α :=
(orthomodularity : ∀ x y : α, x ⊔ (x′ ⊓ (x ⊔ y)) = x ⊔ y)

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

def arrow₀ (a b : α) : α := a′ ⊔ b

infix ` ⟶₀ `:60 := arrow₀

def arrow₁ (a b : α) : α := a′ ⊔ a ⊓ b

infix ` ⟶₁ `:60 := arrow₁

def arrow₂ (a b : α) : α := b ⊔ a′ ⊓ b′

infix ` ⟶₂ `:60 := arrow₂

def arrow₃ (a b : α) : α := (a′ ⊓ b ⊔ a′ ⊓ b′) ⊔ a ⊓ (a′ ⊔ b)

infix ` ⟶₃ `:60 := arrow₃

def arrow₄ (a b : α) : α := (a ⊓ b ⊔ a′ ⊓ b) ⊔ b′ ⊓ (a′ ⊔ b)

infix ` ⟶₄ `:60 := arrow₄

def arrow₅ (a b : α) : α := (a ⊓ b ⊔ a′ ⊓ b) ⊔ a′ ⊓ b′

infix ` ⟶₅ `:60 := arrow₅

def equiv₀ (a b : α) : α := (a′ ⊔ b) ⊓ (b′ ⊔ a) 

infix ` ≣₀ `:59 := equiv₀

def equiv₁ (a b : α) : α := (a ⊔ b′) ⊓ (a′ ⊔ a ⊓ b) 

infix ` ≣₁ `:59 := equiv₁

def equiv₂ (a b : α) : α := (a ⊔ b′) ⊓ (b ⊔ a′ ⊓ b′) 

infix ` ≣₂ `:59 := equiv₂

def equiv₃ (a b : α) : α := (a′ ⊔ b) ⊓ (a ⊔ a′ ⊓ b′) 

infix ` ≣₃ `:59 := equiv₃

def equiv₄ (a b : α) : α := (a′ ⊔ b) ⊓ (b′ ⊔ a ⊓ b) 

infix ` ≣₄ `:59 := equiv₄

def biconditional (a b : α) : α := (a ⊓ b) ⊔ (a′ ⊓ b′) 

infix ` ≣ `:59 := biconditional

def equiv_OA (a b c : α) : α := (a ⟶₁ c) ⊓ (b ⟶₁ c) ⊔ (a′ ⟶₁ c) ⊓ (b′ ⟶₁ c)

notation `≣ᴼᴬ` := equiv_OA

def oml_of_orthomoduler'' (H : ∀ a b : α, a ≤ b → a′ ⊓ b ≤ ⊥ → b ≤ a) : orthomodular_lattice α :=
⟨λ a b, by {
  have : a ⊔ a′ ⊓ (a ⊔ b) ≤ a ⊔ b, { simp },
  refine antisymm this (H _ _ this _),
  calc (a ⊔ a′ ⊓ (a ⊔ b))′ ⊓ (a ⊔ b) = a′ ⊓ (a′ ⊓ (a ⊔ b))′ ⊓ (a ⊔ b)   : by simp[sup_compl]
                                 ... = (a′ ⊓ (a ⊔ b))′ ⊓ (a′ ⊓ (a ⊔ b)) : by simp[@inf_comm _ _ a′, inf_assoc]
                                 ... ≤ ⊥                                : by simp }⟩

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

namespace orthomodular_lattice
variables {α : Type u} [orthomodular_lattice α]
open ortholattice

--attribute [simp] orthomodularity

lemma orthomodularity_dual (a b : α) : a ⊓ (a′ ⊔ (a ⊓ b)) = a ⊓ b :=
by { have : a′ ⊔ a ⊓ (a′ ⊔ b′) = a′ ⊔ b′,
     { have := orthomodularity a′ b′, simp at this, exact this },
     have := congr_arg has_orthocompl.orthocompl this, simp[sup_compl, inf_compl] at this, exact this }

def commutes (a b : α) : Prop := a = (a ⊓ b) ⊔ (a ⊓ b′)

infix ` ⫰ `:50 := commutes

lemma commutes_of_le_sup {a b : α} (h : a ≤ (a ⊓ b) ⊔ (a ⊓ b′)) : a ⫰ b := antisymm h (by simp)

@[simp] lemma commutes.topr (a : α) : a ⫰ ⊤ := commutes_of_le_sup (by simp)

@[simp] lemma commutes.botr (a : α) : a ⫰ ⊥ := commutes_of_le_sup (by simp)

@[simp] lemma commutes.topl (a : α) : ⊤ ⫰ a := commutes_of_le_sup (by simp)

@[simp] lemma commutes.botl (a : α) : ⊥ ⫰ a := commutes_of_le_sup (by simp)

lemma commutes_of_le {a b : α} (h : a ≤ b) : a ⫰ b :=
by { have : a ⊓ b = a, from inf_eq_left.mpr h,
     simp[(⫰), this] }

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

lemma commutes.compll_iff {a b : α} : a′ ⫰ b ↔ a ⫰ b:=
⟨λ h, by { have := h.compll, simp at this, exact this }, λ h, h.compll⟩

lemma commutes_of_ge {a b : α} (h : b ≤ a) : a ⫰ b :=
(commutes_of_le h).symm

lemma commutes.eql_dual {a b : α} (c : a ⫰ b) : (a ⊔ b) ⊓ (a ⊔ b′) = a :=
begin
  have := congr_arg has_orthocompl.orthocompl c.compll.complr,
  simp[inf_compl, sup_compl] at this, exact this.symm
end

lemma commutes_of_dual {a b : α} (h : a = (a ⊔ b) ⊓ (a ⊔ b′)) : a ⫰ b :=
by { have : a′ ⫰ b,
     { have := congr_arg has_orthocompl.orthocompl h,
       simp[inf_compl, sup_compl, @sup_comm _ _ (a′ ⊓ b′)] at this, exact this },
     have := this.compll, simp at this, exact this }

lemma commutes.inf_compl_sup {a b : α} (c : a ⫰ b) :
  a ⊓ (a′ ⊔ b) = a ⊓ b :=
calc a ⊓ (a′ ⊔ b) = a ⊓ (b ⊔ a) ⊓ (b ⊔ a′) : by simp[show a ⊓ (b ⊔ a) = a, by simp, @sup_comm _ _ a′ b]
              ... = a ⊓ b                  : by simp[inf_assoc, c.symm.eql_dual]

theorem Foulis_Holland₁ {a b c : α} (h₁ : a ⫰ b) (h₂ : a ⫰ c) :
  a ⊓ b ⊔ a ⊓ c = a ⊓ (b ⊔ c) :=
begin
  suffices : (a ⊓ b ⊔ a ⊓ c)′ ⊓ (a ⊓ (b ⊔ c)) = ⊥, from orthomodularity'' le_inf_sup this,
  have : a ⊓ (a′ ⊔ b′) ⊓ (a′ ⊔ c′) = a ⊓ b′ ⊓ c′,
    calc a ⊓ (a′ ⊔ b′) ⊓ (a′ ⊔ c′) = a ⊓ b′ ⊓ (a′ ⊔ c′)   : by simp[h₁.complr.inf_compl_sup]
                               ... = b′ ⊓ (a ⊓ (a′ ⊔ c′)) : by simp[@inf_comm _ _ b′, inf_assoc]
                               ... = b′ ⊓ (a ⊓ c′)        : by simp[h₂.complr.inf_compl_sup]
                               ... = a ⊓ b′ ⊓ c′          : by simp[@inf_comm _ _ b′, ←inf_assoc],
  calc  (a ⊓ b ⊔ a ⊓ c)′ ⊓ (a ⊓ (b ⊔ c))
      = (a′ ⊔ b′) ⊓ (a′ ⊔ c′) ⊓ a ⊓ (b ⊔ c) : by simp[sup_compl, inf_compl, inf_assoc]
  ... = a ⊓ (a′ ⊔ b′) ⊓ (a′ ⊔ c′) ⊓ (b ⊔ c) : by simp[@inf_comm _ _ _ a, ←inf_assoc]
  ... = a ⊓ b′ ⊓ c′ ⊓ (b ⊔ c)               : by simp[this]
  ... = a ⊓ (b ⊔ c)′ ⊓ (b ⊔ c)              : by simp[show a ⊓ b′ ⊓ c′ = a ⊓ (b ⊔ c)′, by simp[sup_compl, inf_assoc]]
  ... = ⊥                                   : by simp[inf_assoc]
end

theorem Foulis_Holland₂ {a b c : α} (h₁ : a ⫰ b) (h₂ : a ⫰ c) :
  b ⊓ a ⊔ b ⊓ c = b ⊓ (a ⊔ c) :=
begin
  suffices : (b ⊓ a ⊔ b ⊓ c)′ ⊓ (b ⊓ (a ⊔ c)) = ⊥, from orthomodularity'' le_inf_sup this,
  calc  (b ⊓ a ⊔ b ⊓ c)′ ⊓ (b ⊓ (a ⊔ c))
      = (b′ ⊔ a′) ⊓ (b ⊓ c)′ ⊓ (b ⊓ (a ⊔ c)) : by simp[sup_compl, inf_compl]
  ... = b ⊓ (b′ ⊔ a′) ⊓ (b ⊓ c)′ ⊓ (a ⊔ c)   : by simp[@inf_comm _ _ _ b, ←inf_assoc]
  ... = b ⊓ a′ ⊓ (b ⊓ c)′ ⊓ (a ⊔ c)          : by simp[h₁.symm.complr.inf_compl_sup]
  ... = b ⊓ (a′ ⊓ (a ⊔ c)) ⊓ (b ⊓ c)′        : by simp[inf_assoc, show (b ⊓ c)′ ⊓ (a ⊔ c) = (a ⊔ c) ⊓ (b ⊓ c)′, from inf_comm]
  ... = b ⊓ (a′ ⊓ c) ⊓ (b ⊓ c)′              : by have := h₂.compll.inf_compl_sup; simp at this; simp[this]
  ... = (b ⊓ c)′ ⊓ (b ⊓ (c ⊓ a′))            : by simp[@inf_comm _ _ _ (b ⊓ c)′, @inf_comm _ _ a′]
  ... = (b ⊓ c)′ ⊓ (b ⊓ c) ⊓ a′              : by simp only [inf_assoc]
  ... = ⊥                                    : by simp
end

theorem Foulis_Holland₃ {a b c : α} (h₁ : a ⫰ b) (h₂ : a ⫰ c) :
  (a ⊔ b) ⊓ (a ⊔ c) = a ⊔ (b ⊓ c) :=
begin
  suffices : ((a ⊔ b) ⊓ (a ⊔ c))′ = (a ⊔ (b ⊓ c))′,
  { have := congr_arg has_orthocompl.orthocompl this, simp at this, exact this },
  calc ((a ⊔ b) ⊓ (a ⊔ c))′ = a′ ⊓ b′ ⊔ a′ ⊓ c′ : by simp[sup_compl, inf_compl]
                        ... = a′ ⊓ (b′ ⊔ c′)    : Foulis_Holland₁ h₁.complr.compll h₂.complr.compll
                        ... = (a ⊔ (b ⊓ c))′    : by simp[sup_compl, inf_compl]
end

theorem Foulis_Holland₄ {a b c : α} (h₁ : a ⫰ b) (h₂ : a ⫰ c) :
  (b ⊔ a) ⊓ (b ⊔ c) = b ⊔ (a ⊓ c) :=
begin
  suffices : ((b ⊔ a) ⊓ (b ⊔ c))′ = (b ⊔ (a ⊓ c))′,
  { have := congr_arg has_orthocompl.orthocompl this, simp at this, exact this },
  calc ((b ⊔ a) ⊓ (b ⊔ c))′ = b′ ⊓ a′ ⊔ b′ ⊓ c′ : by simp[sup_compl, inf_compl]
                        ... = b′ ⊓ (a′ ⊔ c′)    : Foulis_Holland₂ h₁.complr.compll h₂.complr.compll
                        ... = (b ⊔ (a ⊓ c))′    : by simp[sup_compl, inf_compl]
end

theorem Foulis_Holland₄' {a b c : α} (h₁ : a ⫰ b) (h₂ : a ⫰ c) :
  (b ⊔ c) ⊓ (b ⊔ a) = b ⊔ (c ⊓ a) :=
by simp[@inf_comm _ _ (b ⊔ c), @inf_comm _ _ c, Foulis_Holland₄ h₁ h₂]

lemma commutes.supr {a b c : α} (h₁ : a ⫰ b) (h₂ : a ⫰ c) : a ⫰ b ⊔ c :=
begin
  suffices : b ⊔ c ⫰ a, from this.symm,
  calc b ⊔ c = (b ⊓ a ⊔ b ⊓ a′) ⊔ (c ⊓ a ⊔ c ⊓ a′) : by simp[h₁.symm.eql, h₂.symm.eql]
         ... = b ⊓ a ⊔ (b ⊓ a′ ⊔ c ⊓ a) ⊔ c ⊓ a′   : by simp[sup_assoc]
         ... = b ⊓ a ⊔ (c ⊓ a ⊔ b ⊓ a′) ⊔ c ⊓ a′   : by simp[@sup_comm _ _ (c ⊓ a) (b ⊓ a′)]
         ... = (a ⊓ b ⊔ a ⊓ c) ⊔ (a′ ⊓ b ⊔ a′ ⊓ c) : by simp[sup_assoc, @inf_comm _ _ b, @inf_comm _ _ c]
         ... = a ⊓ (b ⊔ c) ⊔ a′ ⊓ (b ⊔ c)          : by simp[Foulis_Holland₁ h₁ h₂, Foulis_Holland₁ h₁.compll h₂.compll]
         ... = (b ⊔ c) ⊓ a ⊔ (b ⊔ c) ⊓ a′          : by simp[@inf_comm _ _ _ a, @inf_comm _ _ _ a′]
end

lemma commutes.infr {a b c : α} (h₁ : a ⫰ b) (h₂ : a ⫰ c) : a ⫰ b ⊓ c :=
begin
  have : a ⫰ (b′ ⊔ c′)′, from (h₁.complr.supr h₂.complr).complr,
  simp[sup_compl] at this, exact this
end

lemma commutes.supl {a b c : α} (h₁ : a ⫰ c) (h₂ : b ⫰ c) : a ⊔ b ⫰ c :=
(h₁.symm.supr h₂.symm).symm

lemma commutes.infl {a b c : α} (h₁ : a ⫰ c) (h₂ : b ⫰ c) : a ⊓ b ⫰ c :=
(h₁.symm.infr h₂.symm).symm

theorem Gudder_Schelp {a b c : α} (h₁ : a ⫰ b) (h₂ : b ⫰ c) (h₃ : a ⫰ b ⊓ c) : a ⊓ b ⫰ c :=
begin
  have c₁ : a ⊔ c′ ⫰ b ⊓ c,
    from (h₃.symm.supr (h₂.symm.infr (commutes.refl c)).symm.complr).symm,
  have c₂ : a ⊔ c′ ⫰ a ⊓ b, from (commutes_of_le ((show a ⊓ b ≤ a, by simp).trans (by simp))).symm,
  have c₃ : b ⊓ c ⫰ c′, from h₂.complr.infl (commutes.refl c).complr,
  have eqn₁ : a ⊓ b ⊓ (a ⊔ c′) = a ⊓ b, { simp, from (show a ⊓ b ≤ a, by simp).trans (by simp) },
  have eqn₂ : a ⊓ b ⊓ c = (a ⊔ c′) ⊓ b ⊓ c,
    calc a ⊓ b ⊓ c = b ⊓ c ⊓ a                  : by simp[@inf_comm _ _ a, inf_assoc]
               ... = (b ⊓ c) ⊓ a ⊔ (b ⊓ c) ⊓ c′ : by simp[show (b ⊓ c) ⊓ c′ = ⊥, by simp[inf_assoc]]
               ... = (b ⊓ c) ⊓ (a ⊔ c′)         : Foulis_Holland₁ h₃.symm c₃
               ... = (a ⊔ c′) ⊓ b ⊓ c           : by simp[@inf_comm _ _ (a ⊔ c′), inf_assoc],
  refine commutes_of_dual _,
  calc a ⊓ b = b ⊓ c ⊓ a ⊔ a ⊓ b                           : by simp; simp[inf_assoc]
         ... = a ⊓ b ⊓ c ⊔ a ⊓ b                           : by simp[@inf_comm _ _ _ a, ←inf_assoc]
         ... = (a ⊔ c′) ⊓ b ⊓ c ⊔ a ⊓ b                    : by simp[eqn₂]
         ... = ((a ⊔ c′) ⊓ b ⊓ c) ⊔ (a ⊓ b ⊓ (a ⊔ c′))     : by simp[eqn₁]
         ... = ((a ⊔ c′) ⊓ (b ⊓ c)) ⊔ ((a ⊔ c′) ⊓ (a ⊓ b)) : by simp[@inf_comm _ _ (a ⊓ b), ←inf_assoc]
         ... = (a ⊔ c′) ⊓ (b ⊓ c ⊔ a ⊓ b)                  : Foulis_Holland₁ c₁ c₂
         ... = (a ⊔ c′) ⊓ (b ⊓ c ⊔ b ⊓ a)                  : by simp[@inf_comm _ _ b a]
         ... = (a ⊔ c′) ⊓ (b ⊓ (c ⊔ a))                    : by simp[Foulis_Holland₁ h₂ h₁.symm]
         ... = (a ⊔ c′) ⊓ (c ⊔ a) ⊓ b                      : by simp[@inf_comm _ _ _ b, ←inf_assoc]
         ... = (a ⊔ c′) ⊓ (c ⊔ a) ⊓ ((b ⊔ c) ⊓ (b ⊔ c′))   : by simp[h₂.eql_dual]
         ... = (a ⊔ c′) ⊓ ((c ⊔ a) ⊓ (c ⊔ b)) ⊓ (b ⊔ c′)   : by simp[inf_assoc, @sup_comm _ _ c b]
         ... = (c ⊔ a) ⊓ (c ⊔ b) ⊓ (a ⊔ c′) ⊓ (b ⊔ c′)     : by simp[@inf_comm _ _ ((c ⊔ a) ⊓ (c ⊔ b))]
         ... = (c ⊔ a ⊓ b) ⊓ (a ⊔ c′) ⊓ (b ⊔ c′)           : by simp[Foulis_Holland₄' h₂ h₁.symm]
         ... = (c ⊔ a ⊓ b) ⊓ ((c′ ⊔ a) ⊓ (c′ ⊔ b))         : by simp[@sup_comm _ _ _ c′, inf_assoc]
         ... = (c ⊔ a ⊓ b) ⊓ (c′ ⊔ a ⊓ b)                  : by simp[Foulis_Holland₄' h₂.complr h₁.symm]
         ... = (a ⊓ b ⊔ c) ⊓ (a ⊓ b ⊔ c′)                  : by simp[@sup_comm _ _ c, @sup_comm _ _ c′]
end

theorem Gudder_Schelp_Beran {a b c : α} (h₁ : b ⫰ c) (h₂ : a ⫰ b ⊓ c) : a ⊓ b ⫰ c :=
begin
  have h₃ : a′ ⊔ b′ ⫰ b, from commutes.complr_iff.mp (commutes_of_ge (by simp)),
  have h₄ : a′ ⊔ b′ ⫰ b ⊓ c, from h₂.compll.supl (commutes_of_ge (by simp)).compll,
  have : (a′ ⊔ b′) ⊓ b ⫰ c, from Gudder_Schelp h₃ h₁ h₄,
  have : b′ ⊔ b ⊓ a ⫰ c,
  { have := this.compll, simp[sup_compl, inf_compl] at this,
    simp[@sup_comm _ _ b′, @inf_comm _ _ b],
    exact this },
  have : b ⊓ (b′ ⊔ b ⊓ a) ⫰ c, from h₁.infl this,
  rw[orthomodularity_dual b a, @inf_comm _ _ b a] at this,
  exact this
end

def commutes_set (s : set α) : Prop := ∀ a b ∈ s, a ⫰ b

def gen_set_aux (s : set α) : ℕ → set α
| 0       := s
| (n + 1) :=
    gen_set_aux n ∪ ({⊤, ⊥} ∪
    {a | ∃ b c ∈ gen_set_aux n, a = b ⊔ c} ∪
    {a | ∃ b c ∈ gen_set_aux n, a = b ⊓ c} ∪
    {a | ∃ b ∈ gen_set_aux n, a = b′})

def gen_set (s : set α) := {a | ∃ n, a ∈ gen_set_aux s n}

section
variables (s : set α)

lemma gen_set_aux_mono :
  ∀ {m n : ℕ}, m ≤ n → gen_set_aux s m ⊆ gen_set_aux s n :=
begin
  suffices : ∀ n m, gen_set_aux s m ⊆ gen_set_aux s (m + n),
  { intros m n le a mem, have := this (n - m) m mem,
    simp[nat.add_sub_of_le le] at this, exact this },
  intros n, induction n with n IH; simp[←nat.add_one, ←add_assoc],
  { intros m, refl },
  { intros m,
    have : gen_set_aux s (m + n) ⊆ gen_set_aux s (m + n + 1),
    { simp[gen_set_aux] },
    exact set.subset.trans (IH m) this }
end

@[simp] lemma gen_set_top_mem :
  ⊤ ∈ gen_set s := ⟨1, by simp[gen_set_aux]⟩

@[simp] lemma gen_set_bot_mem :
  ⊥ ∈ gen_set s := ⟨1, by simp[gen_set_aux]⟩

variables {s}

@[simp] lemma gen_set_sup_mem {a b : α}
  (h₁ : a ∈ gen_set s) (h₂ : b ∈ gen_set s) :
  a ⊔ b ∈ gen_set s :=
begin
  rcases h₁ with ⟨n₁, h₁⟩,
  rcases h₂ with ⟨n₂, h₂⟩,
  have mem_a : a ∈ gen_set_aux s (max n₁ n₂), from gen_set_aux_mono s (by simp) h₁,
  have mem_b : b ∈ gen_set_aux s (max n₁ n₂), from gen_set_aux_mono s (by simp) h₂,
  refine ⟨max n₁ n₂ + 1, or.inr $ or.inl $ or.inl $ or.inr ⟨a, mem_a, b, mem_b, rfl⟩⟩
end

@[simp] lemma gen_set_compl_mem {a : α}
  (h : a ∈ gen_set s) : a′ ∈ gen_set s :=
by rcases h with ⟨n, h⟩; refine ⟨n + 1, or.inr $ or.inr ⟨a, h, rfl⟩⟩

@[simp] lemma gen_set_inf_mem {a b : α}
  (h₁ : a ∈ gen_set s) (h₂ : b ∈ gen_set s) :
  a ⊓ b ∈ gen_set s :=
begin
  rcases h₁ with ⟨n₁, h₁⟩,
  rcases h₂ with ⟨n₂, h₂⟩,
  have mem_a : a ∈ gen_set_aux s (max n₁ n₂), from gen_set_aux_mono s (by simp) h₁,
  have mem_b : b ∈ gen_set_aux s (max n₁ n₂), from gen_set_aux_mono s (by simp) h₂,
  refine ⟨max n₁ n₂ + 1, or.inr $ or.inl $ or.inr ⟨a, mem_a, b, mem_b, rfl⟩⟩
end

lemma commutes_set_gen_set (h : commutes_set s) : commutes_set (gen_set s) :=
begin
  suffices : ∀ n, commutes_set (gen_set_aux s n),
  { rintros a ⟨n₁, h₁⟩ b ⟨n₂, h₂⟩,
    have h₁ : a ∈ gen_set_aux s (max n₁ n₂), from gen_set_aux_mono s (by simp) h₁,
    have h₂ : b ∈ gen_set_aux s (max n₁ n₂), from gen_set_aux_mono s (by simp) h₂,
    exact this (max n₁ n₂) a h₁ b h₂ },
  intros n,
  induction n with n IH; simp[gen_set_aux, h],
  intros a h₁ b h₂, simp at h₁ h₂,
  rcases h₁ with
    (h₁ | (((rfl | rfl) | ⟨a₁, h₁₁, a₂, h₁₂, rfl⟩) | ⟨a₁, h₁₁, a₂, h₁₂, rfl⟩) | ⟨a₁, h₁, rfl⟩); try {simp}, 
  { rcases h₂ with
      (h₂ | (((rfl | rfl) | ⟨b₁, h₂₁, b₂, h₂₂, rfl⟩) | ⟨b₁, h₂₁, b₂, h₂₂, rfl⟩) | ⟨b₁, h₂, rfl⟩); try {simp},
    { exact IH _ h₁ _ h₂ },
    { exact (IH _ h₁ _ h₂₁).supr (IH _ h₁ _ h₂₂) },
    { exact (IH _ h₁ _ h₂₁).infr (IH _ h₁ _ h₂₂) },
    { exact (IH _ h₁ _ h₂) } },
  { rcases h₂ with
      (h₂ | (((rfl | rfl) | ⟨b₁, h₂₁, b₂, h₂₂, rfl⟩) | ⟨b₁, h₂₁, b₂, h₂₂, rfl⟩) | ⟨b₁, h₂, rfl⟩); try {simp},
    { exact (IH _ h₁₁ _ h₂).supl (IH _ h₁₂ _ h₂) },
    { exact ((IH _ h₁₁ _ h₂₁).supr (IH _ h₁₁ _ h₂₂)).supl ((IH _ h₁₂ _ h₂₁).supr (IH _ h₁₂ _ h₂₂)) },
    { exact ((IH _ h₁₁ _ h₂₁).infr (IH _ h₁₁ _ h₂₂)).supl ((IH _ h₁₂ _ h₂₁).infr (IH _ h₁₂ _ h₂₂)) },
    { exact (IH _ h₁₁ _ h₂).supl (IH _ h₁₂ _ h₂) } },
  { rcases h₂ with
      (h₂ | (((rfl | rfl) | ⟨b₁, h₂₁, b₂, h₂₂, rfl⟩) | ⟨b₁, h₂₁, b₂, h₂₂, rfl⟩) | ⟨b₁, h₂, rfl⟩); try {simp},
    { exact (IH _ h₁₁ _ h₂).infl (IH _ h₁₂ _ h₂) },
    { exact ((IH _ h₁₁ _ h₂₁).supr (IH _ h₁₁ _ h₂₂)).infl ((IH _ h₁₂ _ h₂₁).supr (IH _ h₁₂ _ h₂₂)) },
    { exact ((IH _ h₁₁ _ h₂₁).infr (IH _ h₁₁ _ h₂₂)).infl ((IH _ h₁₂ _ h₂₁).infr (IH _ h₁₂ _ h₂₂)) },
    { exact (IH _ h₁₁ _ h₂).infl (IH _ h₁₂ _ h₂) } },
  { rcases h₂ with
      (h₂ | (((rfl | rfl) | ⟨b₁, h₂₁, b₂, h₂₂, rfl⟩) | ⟨b₁, h₂₁, b₂, h₂₂, rfl⟩) | ⟨b₁, h₂, rfl⟩); try {simp},
    { exact (IH _ h₁ _ h₂).compll },
    { exact (IH _ h₁ _ h₂₁).compll.supr (IH _ h₁ _ h₂₂).compll },
    { exact (IH _ h₁ _ h₂₁).compll.infr (IH _ h₁ _ h₂₂).compll },
    { exact (IH _ h₁ _ h₂).compll } }
end

end

structure suboml_set (α : Type*) [orthomodular_lattice α] :=
(carrier : α → Prop)
(top : carrier ⊤)
(bot : carrier ⊥)
(sup : ∀ ⦃a b : α⦄, carrier a → carrier b → carrier (a ⊔ b))
(inf : ∀ ⦃a b : α⦄, carrier a → carrier b → carrier (a ⊓ b))
(compl : ∀ ⦃a : α⦄, carrier a → carrier a′)

instance : set_like (suboml_set α) α :=
{ coe := λ s, s.carrier,
  coe_injective' := λ s t, by { cases s; cases t; simp } }

def gen_set' (s : set α) : suboml_set α :=
{ carrier := gen_set s,
  top := gen_set_top_mem s,
  bot := gen_set_bot_mem s,
  sup := @gen_set_sup_mem _ _ s,
  inf := @gen_set_inf_mem _ _ s,
  compl := @gen_set_compl_mem _ _ s }

@[simp] lemma suboml_set_coe_set (s : suboml_set α) : (↑s : set α) = s.carrier := rfl

@[reducible] def suboml (s : suboml_set α) := subtype s.carrier

namespace suboml_set
variables {s : suboml_set α}

instance : lattice (suboml s) := subtype.lattice s.sup s.inf

lemma le_iff_coe_le {a b : suboml s} : a ≤ b ↔ (↑a : α) ≤ b := by refl

lemma eq_iff_coe_eq {a b : suboml s} : a = b ↔ (↑a : α) = b :=
by simp[le_antisymm_iff]

@[simp] lemma mk_le_iff_le {a b : α} {ha} {hb} : (⟨a, ha⟩ : suboml s) ≤ ⟨b, hb⟩ ↔ a ≤ b := by refl

@[simp] lemma mk_eq_iff_eq {a b : α} {ha} {hb} : (⟨a, ha⟩ : suboml s) = ⟨b, hb⟩ ↔ a = b :=
by simp[le_antisymm_iff]

@[simp] lemma coe_sup {a b : suboml s} : ((a ⊔ b : suboml s) : α) = ↑a ⊔ ↑b := by refl

@[simp] lemma sup_coe {a b} {ha} {hb}: (⟨a, ha⟩ : suboml s) ⊔ ⟨b, hb⟩ = ⟨a ⊔ b, s.sup ha hb⟩ := by refl

@[simp] lemma coe_inf {a b : suboml s} : ((a ⊓ b : suboml s) : α) = ↑a ⊓ ↑b := by refl

@[simp] lemma inf_coe {a b} {ha} {hb}: (⟨a, ha⟩ : suboml s) ⊓ ⟨b, hb⟩ = ⟨a ⊓ b, s.inf ha hb⟩ := by refl

instance : bounded_order (suboml s) :=
{ top := ⟨⊤, s.top⟩,
  le_top := λ a, le_iff_coe_le.mpr (by simp),
  bot := ⟨⊥, s.bot⟩,
  bot_le := λ a, le_iff_coe_le.mpr (by simp) }

@[simp] lemma coe_top : ((⊤ : suboml s) : α) = ⊤ := by refl

@[simp] lemma mk_top {h}: (⟨⊤, h⟩ : suboml s) = ⊤ := by refl

@[simp] lemma mk_bot {h}: (⟨⊥, h⟩ : suboml s) = ⊥ := by refl

@[simp] lemma coe_bot : ((⊥ : suboml s) : α) = ⊥ := by refl

instance : has_orthocompl (suboml s) := ⟨λ ⟨a, h⟩, ⟨a′, s.compl h⟩⟩

@[simp] lemma mk_compl (a : α) (h) :
  (⟨a, h⟩ : suboml s)′ = ⟨a′, s.compl h⟩ := rfl

instance : ortholattice (suboml s) :=
{ double_compl := λ ⟨a, h⟩, by simp,
  contraposition := λ ⟨a, ha⟩ ⟨b, hb⟩, by simp; refine contraposition a b,
  sup_compl := λ ⟨a, ha⟩ ⟨b, hb⟩, by simp[sup_compl],
  inf_compl_le_bot := λ ⟨a, h⟩, by simp,
  top_le_sup_compl := λ ⟨a, h⟩, by simp }

instance : orthomodular_lattice (suboml s) :=
⟨λ ⟨a, h⟩ ⟨b, h⟩, by { simp, exact orthomodularity a b }⟩

def distrib_lattice_of_commutes (h : commutes_set (↑s : set α)) :
  distrib_lattice (suboml s) :=
{ le_sup_inf := λ ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩, by simp [Foulis_Holland₃ (h a ha b hb) (h a ha c hc)],
  ..orthomodular_lattice.suboml.lattice }

def boolean_algebra_of_commutes (h : commutes_set (↑s : set α)) :
  boolean_algebra (suboml s) :=
boolean_algebra.of_core
{ compl := λ a, a′,
  inf_compl_le_bot := λ ⟨a, h⟩, by simp,
  top_le_sup_compl := λ ⟨a, h⟩, by simp,
  ..distrib_lattice_of_commutes h,
  ..orthomodular_lattice.suboml.bounded_order }

instance boolean_algebra_of_commutes_gen {s : set α} (h : commutes_set s) :
  boolean_algebra (suboml $ gen_set' s) :=
boolean_algebra_of_commutes (by { simp[gen_set'], refine commutes_set_gen_set h })

end suboml_set

def commutability (a b : α) : α := a ⊓ b ⊔ a′ ⊓ b ⊔ a ⊓ b′ ⊔ a′ ⊓ b′

infix ` ⫫ `:60 := commutability

lemma commutes_iff_commutability_eq_top (a b : α) :
  a ⫰ b ↔ a ⫫ b = ⊤ :=
⟨λ h, by { 
  calc a ⊓ b ⊔ a′ ⊓ b ⊔ a ⊓ b′ ⊔ a′ ⊓ b′ = (a ⊓ b ⊔ a′ ⊓ b) ⊔ (a ⊓ b′ ⊔ a′ ⊓ b′) : by simp[sup_assoc]
                                     ... = (b ⊓ a ⊔ b ⊓ a′) ⊔ (b′ ⊓ a ⊔ b′ ⊓ a′) : by simp[inf_comm]
                                     ... = (b ⊓ (a ⊔ a′)) ⊔ (b′ ⊓ (a ⊔ a′))      : by simp[h.symm.eql, h.symm.compll.eql]
                                     ... = ⊤                                     : by simp
 }, by {
  simp[(⫫)], intros h,
  have : a ⊔ b′ ≤ (a ⊓ b ⊔ a′ ⊓ b) ⊔ (a ⊓ b′ ⊔ a′ ⊓ b′),
  { simp[←sup_assoc, h] },
 }⟩

end orthomodular_lattice

