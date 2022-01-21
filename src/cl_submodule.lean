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

@[simp] lemma submodule.top_topological_closure : (⊤ : submodule 𝕜 E).topological_closure = ⊤ :=
submodule.topological_closure_eq' complete_univ.complete_space_coe

@[simp] lemma submodule.bot_topological_closure : (⊤ : submodule 𝕜 E).topological_closure = ⊤ :=
by simp

@[simp] lemma submodule.orthogonal3 (K : submodule 𝕜 E) : Kᗮᗮᗮ = Kᗮ :=
(Kᗮ).orthogonal_orthogonal

@[simp] lemma submodule.orthogonal_topological_closure_eq_orthogonal (K : submodule 𝕜 E) :
  K.topological_closureᗮ = Kᗮ :=
begin
  have s_cl_o_o : K.topological_closureᗮᗮ = K.topological_closure,
  { have : complete_space K.topological_closure, from K.is_closed_topological_closure.complete_space_coe,
    by exactI K.topological_closure.orthogonal_orthogonal },
  have : K.topological_closureᗮᗮ = Kᗮᗮ, { simp[s_cl_o_o, K.orthogonal_orthogonal_eq_closure] },
  calc K.topological_closureᗮ = K.topological_closureᗮᗮᗮ : by simp[s_cl_o_o]
                          ... = Kᗮᗮᗮ                     : by simp[this]
                          ... = Kᗮ                       : by simp
end

namespace cl_submodule
open submodule

instance : has_coe (cl_submodule 𝕜 E) (submodule 𝕜 E) := ⟨cl_submodule.carrier⟩

@[simp] lemma coe_mk_eq (K : submodule 𝕜 E) (c : complete_space K) :
  (↑({carrier := K, complete := c} : cl_submodule 𝕜 E) : submodule 𝕜 E) = K := rfl


instance inner_product_space (K : cl_submodule 𝕜 E) : inner_product_space 𝕜 K := submodule.inner_product_space K

instance complete_space (K : cl_submodule 𝕜 E) : complete_space K := K.complete

instance complete_space' (K : cl_submodule 𝕜 E) : complete_space (↑K : submodule 𝕜 E) := K.complete

instance : set_like (cl_submodule 𝕜 E) E :=
⟨λ K, ↑K, λ p q h, by { cases p; cases q; congr', simp* at* }⟩

@[simp] lemma le_mk_iff {K L : submodule 𝕜 E} {cK : complete_space K} {cL : complete_space L} :
  ({carrier := K, complete := cK} : cl_submodule 𝕜 E) ≤ ({carrier := L, complete := cL} : cl_submodule 𝕜 E) ↔
  K ≤ L := by refl

@[simp] lemma mem_mk_iff {K : submodule 𝕜 E} {cK : complete_space K} (a : E) :
  a ∈ ({ carrier := K, complete := cK} : cl_submodule 𝕜 E) ↔ a ∈ K := by refl

lemma closure_mem_def {K : cl_submodule 𝕜 E} {x : E} : x ∈ K ↔ x ∈ (K : submodule 𝕜 E) := by unfold_coes; refl

lemma le_coe_iff {K L : cl_submodule 𝕜 E} : (↑K : submodule 𝕜 E) ≤ ↑L ↔ K ≤ L :=
by { rcases K; rcases L, simp }

def closure (K : submodule 𝕜 E) : cl_submodule 𝕜 E :=
{ carrier := K.topological_closure, complete := K.is_closed_topological_closure.complete_space_coe }

lemma ext : ∀ {K L : cl_submodule 𝕜 E} (eq : (K : submodule 𝕜 E) = L), K = L
| ⟨s, _⟩ ⟨t, _⟩ rfl := rfl

lemma closure_eq_of_complete (K : submodule 𝕜 E) [c : complete_space K] :
  closure K = (⟨K, c⟩ : cl_submodule 𝕜 E) := by { refine ext _, simp[closure] }

@[simp] lemma closure_coe_eq (K : cl_submodule 𝕜 E) :
  closure (K : submodule 𝕜 E) = K := by { rcases K with ⟨K, c⟩, simp, exactI closure_eq_of_complete K }

@[simp] lemma coe_closure_eq (K : submodule 𝕜 E) :
  (closure K : submodule 𝕜 E) = K.topological_closure := by simp[closure]

lemma closure_mem_iff {K : submodule 𝕜 E} {x : E} : x ∈ closure K ↔ x ∈ K.topological_closure :=
by simp[closure_mem_def, closure]

lemma le_closure_mono {K L : submodule 𝕜 E} (le : K ≤ L) : closure K ≤ closure L :=
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
⟨λ K, {carrier := (↑K)ᗮ, complete := submodule.orthogonal.complete_space _}⟩

lemma sup_coe (K L : cl_submodule 𝕜 E) :
  (↑(K ⊔ L) : submodule 𝕜 E) = (↑K ⊔ ↑L : submodule 𝕜 E).topological_closure := by refl

lemma inf_coe (K L : cl_submodule 𝕜 E) :
  (↑(K ⊓ L) : submodule 𝕜 E) = (↑K ⊓ ↑L : submodule 𝕜 E).topological_closure := by refl

lemma Sup_coe (s : set (cl_submodule 𝕜 E)) :
  (↑(Sup s) : submodule 𝕜 E) = (⨆ x ∈ s, (x : submodule 𝕜 E)).topological_closure :=
by { show (Sup (coe '' s : set (submodule 𝕜 E))).topological_closure = (⨆ x ∈ s, (x : submodule 𝕜 E)).topological_closure,
     simp[Sup_image] }

lemma Sup_coe' (s : set (cl_submodule 𝕜 E)) :
  (↑(Sup s) : submodule 𝕜 E) = (⨆ x : s, (x : submodule 𝕜 E)).topological_closure :=
by { show (Sup (coe '' s : set (submodule 𝕜 E))).topological_closure = (⨆ x : s, (x : submodule 𝕜 E)).topological_closure,
     simp[Sup_image'] }

lemma supr_coe {ι} (f : ι → cl_submodule 𝕜 E) :
  (↑(supr f) : submodule 𝕜 E) = (⨆ i, (f i : submodule 𝕜 E)).topological_closure :=
by { show (↑(Sup (set.range f)) : submodule 𝕜 E) = (⨆ i, (f i : submodule 𝕜 E)).topological_closure,
     simp[Sup_coe, show (⨆ x i (h : f i = x), (x : submodule 𝕜 E)) = (⨆ i x (h : f i = x), (x : submodule 𝕜 E)), from supr_comm] }

lemma Inf_coe (s : set (cl_submodule 𝕜 E)) :
  (↑(Inf s) : submodule 𝕜 E) = (⨅ x ∈ s, (x : submodule 𝕜 E)).topological_closure :=
by { show (Inf (coe '' s : set (submodule 𝕜 E))).topological_closure = (⨅ x ∈ s, (x : submodule 𝕜 E)).topological_closure,
     simp[Inf_image] }

lemma Inf_coe' (s : set (cl_submodule 𝕜 E)) :
  (↑(Inf s) : submodule 𝕜 E) = (⨅ x : s, (x : submodule 𝕜 E)).topological_closure :=
by { show (Inf (coe '' s : set (submodule 𝕜 E))).topological_closure = (⨅ x : s, (x : submodule 𝕜 E)).topological_closure,
     simp[Inf_image'] }

lemma infi_coe {ι} (f : ι → cl_submodule 𝕜 E) :
  (↑(infi f) : submodule 𝕜 E) = (⨅ i, (f i : submodule 𝕜 E)).topological_closure :=
by { show (↑(Inf (set.range f)) : submodule 𝕜 E) = (⨅ i, (f i : submodule 𝕜 E)).topological_closure,
     simp[Inf_coe, show (⨅ x i (h : f i = x), (x : submodule 𝕜 E)) = (⨅ i x (h : f i = x), (x : submodule 𝕜 E)), from infi_comm] }

@[simp] lemma compl_coe (K : cl_submodule 𝕜 E) : (↑(K′) : submodule 𝕜 E) = (↑K)ᗮ := by refl

instance : complete_ortholattice (cl_submodule 𝕜 E) :=
{ double_compl := λ a, ext (by simp),
  contraposition := λ a b h, le_coe_iff.mp (by { simp, exact submodule.orthogonal_le (le_coe_iff.mpr h) }),
  sup_compl := λ a b, ext (by simp[sup_coe, inf_coe, submodule.inf_orthogonal]),
  Sup_compl := λ s, by simp[←infi_subtype''];
    exact ext (by simp[Sup_coe', infi_coe, submodule.infi_orthogonal]),
  inf_compl_le_bot := λ a, le_coe_iff.mp (by simp[inf_coe, submodule.inf_orthogonal_eq_bot]),
  top_le_sup_compl := λ a, le_coe_iff.mp (by simp[sup_coe, submodule.sup_orthogonal_of_complete_space]) }

instance : orthomodular_lattice (cl_submodule 𝕜 E) := ortholattice.oml_of_orthomoduler'' (
  begin
    rintros ⟨K, cK⟩ ⟨L, cL⟩ le h v y_z_in_L, simp[inf_coe] at le y_z_in_L ⊢,
    have eq_bot : Kᗮ ⊓ L = ⊥,
    { have h' := le_coe_iff.mpr h, simp[inf_coe] at h',
      have : Kᗮ ⊓ L ≤ (Kᗮ ⊓ L).topological_closure, from (Kᗮ ⊓ L).submodule_topological_closure,
      simp[h'] at this, exact this },
    have : ∃ (y ∈ K) (z ∈ Kᗮ), v = y + z, from by exactI K.exists_sum_mem_mem_orthogonal v,
    rcases this with ⟨y, y_in_K, z, z_in_Ko, rfl⟩,
    have : z ∈ Kᗮ ⊓ L,
    { simp[z_in_Ko],
      have : (y + z) - y ∈ L, exact L.sub_mem y_z_in_L (le y_in_K), 
      simp[add_sub_cancel' y z] at this, exact this },
    simp[eq_bot] at this, rcases this with rfl,
    simp[y_in_K]
  end)




end cl_submodule

end inner_product_space