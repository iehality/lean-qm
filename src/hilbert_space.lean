import analysis.inner_product_space.basic
import analysis.inner_product_space.projection
import analysis.inner_product_space.dual
import analysis.normed_space.dual
import data.real.nnreal
import order.filter.ultrafilter
import order.filter.partial
import algebra.support
import linear_algebra.eigenspace
universes u v

noncomputable theory
open_locale classical

namespace inner_product_space

open is_R_or_C continuous_linear_map

variables {𝕜 : Type u} [is_R_or_C 𝕜] {E : Type v} [inner_product_space 𝕜 E]

local notation `⋆` := (star_ring_aut : ring_aut 𝕜)

local notation `⟪`x`, `y`⟫` := @inner 𝕜 E _ x y

notation `〈` x `|`:= inner_right x

@[reducible] def operator (𝕜 : Type u) [is_R_or_C 𝕜] (E : Type v) [inner_product_space 𝕜 E] := E →L[𝕜] E

variables [complete_space E]

lemma inner_right_norm (x : E) : ∥@inner_right 𝕜 E _ _ x∥ ≤ ∥x∥ :=
continuous_linear_map.op_norm_le_bound _ (norm_nonneg x) (λ x, by simp[norm_inner_le_norm])

def adjoint (A : operator 𝕜 E) : operator 𝕜 E :=
let to_dual' : E →ₛₗ[(⋆ : 𝕜 →+* 𝕜)] normed_space.dual 𝕜 E := 
      { to_fun := λ x, ((〈x|).comp A),
        map_add' := λ x y, by { ext z, simp only [continuous_linear_map.comp_apply, inner_right_apply, inner_add_left], refl }, 
        map_smul' := λ c x, by { 
          ext y, simp only [continuous_linear_map.comp_apply, inner_right_apply, inner_smul_left,continuous_linear_map.smul_apply,
            continuous_linear_map.comp_apply, inner_right_apply], refl } },
    A' := (to_dual 𝕜 E).symm.to_linear_equiv.to_linear_map.comp to_dual' in
begin
  have : continuous A', 
    from linear_map.continuous_of_bound A' (∥A∥) (λ x, by { simp [A'],
      calc
        ∥(〈x|).comp A∥ ≤ ∥〈x|∥ * ∥A∥ : continuous_linear_map.op_norm_comp_le _ _
                   ... ≤ ∥x∥ * ∥A∥   : ordered_ring.mul_le_mul_of_nonneg_right (inner_right_norm x) (norm_nonneg _)
                   ... = ∥A∥ * ∥x∥   : mul_comm ∥x∥ ∥A∥ }),
  exact { to_linear_map := A', cont := this }
end

postfix `†`:90 := adjoint

variables (𝕜)

theorem to_dual_symm_apply (d : E →L[𝕜] 𝕜) (x : E) : ⟪(to_dual 𝕜 E).symm d, x⟫ = d x :=
by { have : (to_dual 𝕜 E) ((to_dual 𝕜 E).symm d) x = d x,
       from congr_fun (congr_arg coe_fn ((to_dual 𝕜 E).to_linear_equiv.right_inv d)) x,
     simp only [to_dual_apply] at this, exact this }

variables {𝕜}

lemma adjoint_left (A : operator 𝕜 E) (x y : E) : ⟪A† x, y⟫ = ⟪x, A y⟫ := by simp [adjoint, to_dual_symm_apply]

lemma adjoint_right (A : operator 𝕜 E) (x y : E) : ⟪x, A† y⟫ = ⟪A x, y⟫ := by { 
  have : ⋆⟪A† y, x⟫ = ⋆⟪y, A x⟫, from congr_arg ⋆ (adjoint_left A y x),
  simp only [inner_conj_sym] at this, exact this }

lemma operator_ext_left (A B : operator 𝕜 E) (h : ∀ x y, ⟪A x, y⟫ = ⟪B x, y⟫) : A = B :=
begin
  ext x,
  have eqn : 〈A x| = 〈B x|, { ext y, simp, exact h x y },
  have : (to_dual 𝕜 E).to_linear_equiv.inv_fun 〈A x| = A x, from (to_dual 𝕜 E).to_linear_equiv.left_inv (A x),
  rw [←this, eqn], exact (to_dual 𝕜 E).to_linear_equiv.left_inv (B x)
end

lemma operator_ext_right (A B : operator 𝕜 E) (h : ∀ x y, ⟪x, A y⟫ = ⟪x, B y⟫) : A = B :=
operator_ext_left A B (λ x y, by {
  have : ⋆⟪y, A x⟫ = ⋆⟪y, B x⟫, from congr_arg ⋆ (h y x), simp only [inner_conj_sym] at this,
  exact this })

lemma adjoint_add (A B : operator 𝕜 E) : (A + B)† = A† + B† := operator_ext_left ((A + B)†) (A† + B†)
begin
  intros x y, simp only [adjoint_left],
  calc ⟪x, A y + B y⟫ = ⟪x, A y⟫ + ⟪x, B y⟫   : by simp only [inner_add_right]
                  ... = ⟪A† x, y⟫ + ⟪B† x, y⟫ : by simp only [adjoint_left]
                  ... = ⟪A† x + B† x, y⟫      : by simp only [inner_add_left]
end

lemma adjoint_mul (A B : operator 𝕜 E) : (A * B)† = B† * A† := operator_ext_left ((A * B)†) (B† * A†)
begin
  intros x y, simp only [adjoint_left],
  calc ⟪x, A (B y)⟫ = ⟪A† x, B y⟫    : by simp only [adjoint_left]
                ... = ⟪B† (A† x), y⟫ : by simp only [adjoint_left]
end

lemma adjoint_smul (A : operator 𝕜 E) (k : 𝕜) : (k • A)† = ⋆k • A† := operator_ext_left ((k • A)†) (⋆k • A†)
begin
  intros x y, simp only [adjoint_left],
  calc ⟪x, k • A y⟫ = k * ⟪x, A y⟫   : by simp only [inner_smul_right]
                ... = k * ⟪A† x, y⟫  : by simp only [adjoint_left]
                ... = ⟪⋆k • A† x, y⟫ : by simp [inner_smul_left]
end

@[simp] lemma adjoint_adjoint (A : operator 𝕜 E) : A†† = A := operator_ext_left (A††) A
(λ x y, by simp only [adjoint_left, adjoint_right])

def is_hermitian (A : operator 𝕜 E) : Prop := A† = A

def is_hermitian_of_eq (A : operator 𝕜 E) (h : ∀ x y, ⟪x, A y⟫ = ⟪A x, y⟫) : is_hermitian A :=
operator_ext_left (A†) A (λ x y, by simp only [adjoint_left, h])

section
variables {ι : Type*} (𝕜)

include 𝕜

def complete_orthonormal (v : ι → E) : Prop := orthonormal 𝕜 v ∧ (∀ x, (∀ i, ⟪x, v i⟫ = 0) → x = 0)

omit 𝕜
variables {𝕜}

lemma complete_orthonormal_maximal {v u : set E} (ss : v ⊆ u)
  (hv : complete_orthonormal 𝕜 (coe : v → E)) (hu : orthonormal 𝕜 (coe : u → E)) : u = v :=
begin
  suffices : u ⊆ v, { exact antisymm this ss },
  intros x mem,
  by_contradiction A,
  have : x = 0, from hv.2 x (λ i, by { show ⟪↑(⟨x, mem⟩ : u), ↑(⟨i, ss i.property⟩ : u)⟫ = 0, 
    refine hu.2 _, simp, rintros rfl, exact A i.property }),
  have : x ≠ 0, from orthonormal.ne_zero hu ⟨x, mem⟩, contradiction
end

end 

lemma submodule.is_closed_orthogonal (K : submodule 𝕜 E) : is_closed (Kᗮ : set E) :=
begin
  rw orthogonal_eq_inter K,
  convert is_closed_Inter (λ v : K, (inner_right (v:E)).is_closed_ker),
  simp
end

def eigenspace (A : operator 𝕜 E) (k : 𝕜) : submodule 𝕜 E := (A - lsmul 𝕜 𝕜 k).ker

lemma eigenspace_eq (A : operator 𝕜 E) (k : 𝕜)  : eigenspace A k = module.End.eigenspace (A.to_linear_map) k := rfl

instance eigenspace_complete (A : operator 𝕜 E) (k : 𝕜) : complete_space (eigenspace A k) :=
continuous_linear_map.complete_space_ker (A - lsmul 𝕜 𝕜 k)

def density (A : operator 𝕜 E) (k : 𝕜) (φ : E) : ℝ := ∥orthogonal_projection (eigenspace A k) φ∥^2

end inner_product_space


