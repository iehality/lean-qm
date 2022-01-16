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

--attribute [simp] orthomodularity

lemma orthomodularity_dual (a b : α) : a ⊓ (a′ ⊔ (a ⊓ b)) = a ⊓ b :=
by { have : a′ ⊔ a ⊓ (a′ ⊔ b′) = a′ ⊔ b′,
     { have := orthomodularity a′ b′, simp at this, exact this },
     have := congr_arg has_orthocompl.orthocompl this, simp[sup_compl, inf_compl] at this, exact this }

def commutes (a b : α) : Prop := a = (a ⊓ b) ⊔ (a ⊓ b′)

infix ` ⫰ `:50 := commutes

lemma commutes_of_le_sup {a b : α} (h : a ≤ (a ⊓ b) ⊔ (a ⊓ b′)) : a ⫰ b := antisymm h (by simp)

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
  simp[(⫰)],
  have c₁ : a ⊔ c′ ⫰ b ⊓ c,
    from (h₃.symm.supr (h₂.symm.infr (commutes.refl c)).symm.complr).symm,
  have c₂ : a ⊔ c′ ⫰ a ⊓ b, from (commutes_of_le ((show a ⊓ b ≤ a, by simp).trans (by simp))).symm,
  have c₃ : b ⊓ c ⫰ c′, from h₂.complr.infl (commutes.refl c).complr,
  have eqn₁ : a ⊓ b ⊓ (a ⊔ c′) = a ⊓ b, { simp, from (show a ⊓ b ≤ a, by simp).trans (by simp) },
  have eqn₂ : a ⊓ b ⊓ c = (a ⊔ c′) ⊓ b ⊓ c, { 
    calc a ⊓ b ⊓ c = b ⊓ c ⊓ a : by simp[@inf_comm _ _ a, inf_assoc]
               ... = (b ⊓ c) ⊓ a ⊔ (b ⊓ c) ⊓ c′ : by simp[show (b ⊓ c) ⊓ c′ = ⊥, by simp[inf_assoc]]
               ... = (b ⊓ c) ⊓ (a ⊔ c′) : Foulis_Holland₁ h₃.symm c₃
               ... = (a ⊔ c′) ⊓ b ⊓ c : by simp[@inf_comm _ _ (a ⊔ c′), inf_assoc]
   },
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
  simp[(⫰)],
  calc a ⊓ b = b ⊓ a : inf_comm
         ... = b ⊓ (b′ ⊔ (b ⊓ a)) : eq.symm (orthomodularity_dual _ _)
         ... = 
         ... = a ⊓ b ⊓ c ⊔ a ⊓ b ⊓ c′ : by sorry
end

end orthomodular_lattice

