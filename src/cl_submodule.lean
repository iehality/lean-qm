import hilbert_space
import quantum_logic


universes u v

noncomputable theory
open_locale classical

namespace inner_product_space

variables (𝕜 : Type u) [is_R_or_C 𝕜] (E : Type v) [inner_product_space 𝕜 E] [complete_space E]

local notation `⋆` := (star_ring_aut : ring_aut 𝕜)

local notation `⟪`x`, `y`⟫` := @inner 𝕜 E _ x y

local notation `〈` x `|`:= innerSL x

local notation `𝑖` := @is_R_or_C.I 𝕜 _

structure cl_submodule :=
(carrier : submodule 𝕜 E)
(complete : complete_space carrier)

variables {𝕜} {E}

@[simp] lemma submodule_top_topological_closure : (⊤ : submodule 𝕜 E).topological_closure = ⊤ :=
submodule.topological_closure_eq' complete_univ.complete_space_coe

@[simp] lemma submodule_bot_topological_closure : (⊤ : submodule 𝕜 E).topological_closure = ⊤ :=
by simp

namespace cl_submodule
open submodule

instance : has_coe (cl_submodule 𝕜 E) (submodule 𝕜 E) := ⟨cl_submodule.carrier⟩

@[simp] lemma coe_mk_eq (s : submodule 𝕜 E) (c : complete_space s) :
  (↑({carrier := s, complete := c} : cl_submodule 𝕜 E) : submodule 𝕜 E) = s := rfl

instance inner_product_space (K : cl_submodule 𝕜 E) : inner_product_space 𝕜 K := submodule.inner_product_space K

instance complete_space (K : cl_submodule 𝕜 E) : complete_space K := K.complete

instance complete_space' (K : cl_submodule 𝕜 E) : complete_space (↑K : submodule 𝕜 E) := K.complete

instance : set_like (cl_submodule 𝕜 E) E :=
⟨λ s, ↑s, λ p q h, by { cases p; cases q; congr', simp* at* }⟩

@[simp] lemma le_mk_iff {s t : submodule 𝕜 E} {cs : complete_space s} {ct : complete_space t} :
  ({carrier := s, complete := cs} : cl_submodule 𝕜 E) ≤ ({carrier := t, complete := ct} : cl_submodule 𝕜 E) ↔ s ≤ t := 
by refl

lemma closure_mem_def {s : cl_submodule 𝕜 E} {x : E} : x ∈ s ↔ x ∈ (s : submodule 𝕜 E) := by unfold_coes; refl

lemma le_coe_iff {s t : cl_submodule 𝕜 E} : (↑s : submodule 𝕜 E) ≤ ↑t ↔ s ≤ t :=
by { rcases s; rcases t, simp }

def closure (s : submodule 𝕜 E) : cl_submodule 𝕜 E :=
{ carrier := s.topological_closure, complete := s.is_closed_topological_closure.complete_space_coe }

lemma ext : ∀ {s t : cl_submodule 𝕜 E} (eq : (s : submodule 𝕜 E) = t), s = t
| ⟨s, _⟩ ⟨t, _⟩ rfl := rfl

lemma closure_eq_of_complete (s : submodule 𝕜 E) [c : complete_space s] :
  closure s = (⟨s, c⟩ : cl_submodule 𝕜 E) := by { refine ext _, simp[closure] }

@[simp] lemma closure_coe_eq (s : cl_submodule 𝕜 E) :
  closure (s : submodule 𝕜 E) = s := by { rcases s with ⟨s, c⟩, simp, exactI closure_eq_of_complete s }

@[simp] lemma coe_closure_eq (s : submodule 𝕜 E) :
  (closure s : submodule 𝕜 E) = s.topological_closure := by simp[closure]

lemma closure_mem_iff {s : submodule 𝕜 E} {x : E} : x ∈ closure s ↔ x ∈ s.topological_closure :=
by simp[closure_mem_def, closure]

lemma le_closure_mono {s t : submodule 𝕜 E} (le : s ≤ t) : closure s ≤ closure t :=
λ x h, by { simp only [closure_mem_iff] at h ⊢, exact submodule.topological_closure_mono le h }

instance : complete_lattice (cl_submodule 𝕜 E) :=
{ sup := λ a b, closure ((a : submodule 𝕜 E) ⊔ b),
  inf := λ a b, closure ((a : submodule 𝕜 E) ⊓ b),
  le_sup_left := λ a b, by {
    have : closure (a : submodule 𝕜 E) ≤ closure (a ⊔ b), from le_closure_mono (by simp),
    simp at this, exact this },
  le_sup_right := λ a b, by {
    have : closure (b : submodule 𝕜 E) ≤ closure (a ⊔ b), from le_closure_mono (by simp),
    simp at this, exact this },
  sup_le := λ a b c h₁ h₂, by { simp,
    have : closure (a ⊔ b : submodule 𝕜 E) ≤ closure c,
      from le_closure_mono (sup_le (le_coe_iff.mpr h₁) (le_coe_iff.mpr h₂)),
    simp at this, exact this },
  inf_le_left := λ a b, by { simp, 
    have : closure (a ⊓ b : submodule 𝕜 E) ≤ closure a, from le_closure_mono (by simp),
    simp at this, exact this },
  inf_le_right := λ a b, by { simp, 
    have : closure (a ⊓ b : submodule 𝕜 E) ≤ closure b, from le_closure_mono (by simp),
    simp at this, exact this },
  le_inf := λ a b c h₁ h₂, by { 
        have : closure (a : submodule 𝕜 E) ≤ closure (b ⊓ c),
      from le_closure_mono (le_inf (le_coe_iff.mpr h₁) (le_coe_iff.mpr h₂)),
    simp at this, exact this },
  Sup := λ S, closure (Sup (coe '' S : set (submodule 𝕜 E))),
  le_Sup := λ S a h, by { 
    have : (a : submodule 𝕜 E) ∈ (coe '' S : set (submodule 𝕜 E)), from ⟨a, h, rfl⟩,
    have : closure ↑a ≤ closure (Sup (coe '' S)), from le_closure_mono (le_Sup this),
    simp at this, exact this },
  Sup_le := λ S a h, by { 
    have : ∀ (b : submodule 𝕜 E), b ∈ (coe '' S : set (submodule 𝕜 E)) → (b : submodule 𝕜 E) ≤ a,
    { rintros _ ⟨b, hb, rfl⟩, simp[le_coe_iff], exact h _ hb },
    have : closure (Sup (coe '' S)) ≤ closure ↑a, from le_closure_mono (Sup_le this),
    simp at this, exact this },
  Inf := λ S, closure (Inf (coe '' S : set (submodule 𝕜 E))),
  Inf_le := λ S a h, by { 
    have : (a : submodule 𝕜 E) ∈ (coe '' S : set (submodule 𝕜 E)), from ⟨a, h, rfl⟩,
    have : closure (Inf (coe '' S)) ≤ closure ↑a, from le_closure_mono (Inf_le this),
    simp at this, exact this },
  le_Inf := λ S a h, by { 
    have : ∀ (b : submodule 𝕜 E), b ∈ (coe '' S : set (submodule 𝕜 E)) → (a : submodule 𝕜 E) ≤ b,
    { rintros _ ⟨b, hb, rfl⟩, simp[le_coe_iff], exact h _ hb },
    have : closure ↑a ≤ closure (Inf (coe '' S)), from le_closure_mono (le_Inf this),
    simp at this, exact this },
  top := closure ⊤,
  bot := closure ⊥,
  le_top := λ a, by {
    have : closure (a : submodule 𝕜 E) ≤ closure ⊤, from le_closure_mono (by simp),
    simp at this, exact this },
  bot_le := λ a, by {
    have : closure (⊥ : submodule 𝕜 E) ≤ closure a, from le_closure_mono (by simp),
    simp at this, exact this },
  ..set_like.partial_order }

@[simp] lemma top_coe : (↑(⊤ : cl_submodule 𝕜 E) : submodule 𝕜 E) = ⊤ :=
by { show (↑(closure ⊤ : cl_submodule 𝕜 E) : submodule 𝕜 E) = ⊤, simp }

@[simp] lemma bot_coe : (↑(⊥ : cl_submodule 𝕜 E) : submodule 𝕜 E) = ⊥ :=
by { show (↑(closure ⊥ : cl_submodule 𝕜 E) : submodule 𝕜 E) = ⊥, simp }

instance : has_orthocompl (cl_submodule 𝕜 E) :=
⟨λ s, {carrier := (↑s)ᗮ, complete := submodule.orthogonal.complete_space _}⟩

lemma sup_coe (s t : cl_submodule 𝕜 E) :
  (↑(s ⊔ t) : submodule 𝕜 E) = (↑s ⊔ ↑t : submodule 𝕜 E).topological_closure := by refl

lemma inf_coe (s t : cl_submodule 𝕜 E) :
  (↑(s ⊓ t) : submodule 𝕜 E) = (↑s ⊓ ↑t : submodule 𝕜 E).topological_closure := by refl

@[simp] lemma compl_coe (s : cl_submodule 𝕜 E) : (↑(s′) : submodule 𝕜 E) = (↑s)ᗮ := by refl

@[simp] lemma double_compl (s : cl_submodule 𝕜 E) : s′′ = s := ext (by simp)

@[simp] lemma sup_compl_eq_top (s : cl_submodule 𝕜 E) : s ⊔ s′ = ⊤ :=
ext (by simp[sup_coe, submodule.sup_orthogonal_of_complete_space])

@[simp] lemma inf_compl_eq_bot (s : cl_submodule 𝕜 E) : s ⊓ s′ = ⊥ :=
ext (by simp[inf_coe, submodule.inf_orthogonal_eq_bot])

lemma contraposition (s t : cl_submodule 𝕜 E) : s ≤ t → t′ ≤ s′ := λ h,
le_coe_iff.mp (by { simp, exact submodule.orthogonal_le (le_coe_iff.mpr h) })

end cl_submodule

end inner_product_space