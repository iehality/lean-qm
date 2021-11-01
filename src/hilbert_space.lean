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

namespace continuous_linear_map
variables
{R₁ : Type*} [semiring R₁]
{R₂ : Type*} [semiring R₂]
{R₃ : Type*} [semiring R₃]
{R₄ : Type*} [semiring R₄]
{σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃}
{σ₃₄ : R₃ →+* R₄}
{M₁ : Type*} [topological_space M₁] [add_comm_monoid M₁]
{M₂ : Type*} [topological_space M₂] [add_comm_monoid M₂]
{M₃ : Type*} [topological_space M₃] [add_comm_monoid M₃]
{M₄ : Type*} [topological_space M₄] [add_comm_monoid M₄]
[module R₁ M₁] [module R₂ M₂]
[module R₃ M₃] [module R₄ M₄]

def dom_restrict (f : M₁ →SL[σ₁₂] M₂) (K : submodule R₁ M₁) :
  K →SL[σ₁₂] M₂ := f.comp (subtype_val K)

@[simp] lemma dom_restrict_apply (f : M₁ →SL[σ₁₂] M₂) (K : submodule R₁ M₁) (x : K) :
  f.dom_restrict K x = f x := rfl

def restrict (f : M₁ →SL[σ₁₂] M₂) (K₁ : submodule R₁ M₁) (K₂ : submodule R₂ M₂) (hf : ∀ x ∈ K₁, f x ∈ K₂) : K₁ →SL[σ₁₂] K₂ :=
(f.dom_restrict K₁).cod_restrict K₂ $ set_like.forall.2 hf

@[simp] lemma restrict_apply
  {f : M₁ →SL[σ₁₂] M₂} {K₁ : submodule R₁ M₁} {K₂ : submodule R₂ M₂} (hf : ∀ x ∈ K₁, f x ∈ K₂) (x : K₁) :
  f.restrict K₁ K₂ hf x = ⟨f x, hf x.1 x.2⟩ := rfl

--lemma lsmul_mul [nondiscrete_normed_field R₁] [is_scalar_tower R₁ R₁ M₁] [normed_algebra R₁ R₁]
-- (c₁ c₂ : R₁) : ((lsmul R₁ R₁ : R₁ →L[R₁] M₁ →L[R₁] M₁) c₁) * (lsmul R₁ R₁ c₁) = lsmul R₁ R₁ (c₁ * c₂)

def power (f : M₁ →L[R₁] M₁) : ℕ → M₁ →L[R₁] M₁
| 0       := 1
| (n + 1) := power n * f

lemma power_zero (f : M₁ →L[R₁] M₁) : power f 0 = 1 := rfl

lemma power_one (f : M₁ →L[R₁] M₁) : power f 1 = f := by ext x; simp only [power, mul_apply, one_apply]

lemma power_two (f : M₁ →L[R₁] M₁) : power f 2 = f * f := by ext x; simp only [power, mul_apply, one_apply]

lemma power_mul (f : M₁ →L[R₁] M₁) (n m : ℕ) : power f m * power f n = power f (m + n) :=
by { induction n with n IH, { ext x, simp only [power_zero, mul_apply, one_apply], refl },
     { simp only [←nat.add_one, ←add_assoc, power, mul_def] at IH ⊢, rw [←comp_assoc, IH] }}

lemma power_mul_one (f : M₁ →L[R₁] M₁) (n : ℕ) : f * power f n = power f (n + 1) :=
calc f * power f n = power f 1 * power f n : by simp only [power_one]
               ... = power f (n + 1)       : by simp only [power_mul, add_comm n 1]


end continuous_linear_map

namespace inner_product_space

open is_R_or_C continuous_linear_map

variables (𝕜 : Type u) [is_R_or_C 𝕜] (E : Type v) [inner_product_space 𝕜 E]

local notation `⋆` := (star_ring_aut : ring_aut 𝕜)

local notation `⟪`x`, `y`⟫` := @inner 𝕜 E _ x y

notation `〈` x `|`:= inner_right x

notation `𝑖` := is_R_or_C.I

@[reducible] def operator := E →L[𝕜] E

variables {𝕜} {E}
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

lemma adjoint_zero : (0 : operator 𝕜 E)† = 0 :=
operator_ext_left _ _ (λ x y, by simp only [adjoint_left, zero_apply, inner_zero_left, inner_zero_right])

lemma adjoint_one : (1 : operator 𝕜 E)† = 1 :=
operator_ext_left _ _ (λ x y, by simp only [adjoint_left, one_apply])

lemma adjoint_add (A B : operator 𝕜 E) : (A + B)† = A† + B† := operator_ext_left ((A + B)†) (A† + B†)
begin
  intros x y, simp only [adjoint_left],
  calc ⟪x, A y + B y⟫ = ⟪x, A y⟫ + ⟪x, B y⟫   : by simp only [inner_add_right]
                  ... = ⟪A† x, y⟫ + ⟪B† x, y⟫ : by simp only [adjoint_left]
                  ... = ⟪A† x + B† x, y⟫      : by simp only [inner_add_left]
end

lemma adjoint_sub (A B : operator 𝕜 E) : (A - B)† = A† - B† := operator_ext_left ((A - B)†) (A† - B†)
begin
  intros x y, simp only [adjoint_left],
  calc ⟪x, A y - B y⟫ = ⟪x, A y⟫ - ⟪x, B y⟫   : by simp only [inner_sub_right]
                  ... = ⟪A† x, y⟫ - ⟪B† x, y⟫ : by simp only [adjoint_left]
                  ... = ⟪A† x - B† x, y⟫      : by simp only [inner_sub_left]
end

lemma adjoint_mul (A B : operator 𝕜 E) : (A * B)† = B† * A† := operator_ext_left ((A * B)†) (B† * A†)
begin
  intros x y, simp only [adjoint_left],
  calc ⟪x, A (B y)⟫ = ⟪A† x, B y⟫    : by simp only [adjoint_left]
                ... = ⟪B† (A† x), y⟫ : by simp only [adjoint_left]
end

lemma adjoint_power (A : operator 𝕜 E) (n : ℕ) : (power A n)† = power (A†) n :=
begin
  induction n with n IH,
  { simp only [power_zero, adjoint_one] },
  { simp only [power, adjoint_mul, IH, power_mul_one] }
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

def is_hermitian (A : operator 𝕜 E) : Prop := ∀ x y, ⟪x, A y⟫ = ⟪A x, y⟫

def is_hermitian_iff {A : operator 𝕜 E} : is_hermitian A ↔ A† = A :=
⟨λ h, operator_ext_left (A†) A (λ x y, by simp only [adjoint_left, h x y]), λ h x y, by simp only [←adjoint_left, h]⟩

structure hermitian (𝕜 : Type u) [is_R_or_C 𝕜] (E : Type v) [inner_product_space 𝕜 E] [complete_space E] :=
(operator : operator 𝕜 E)
(self : is_hermitian operator)

def square_is_hermitian (A : operator 𝕜 E) (h : is_hermitian A) : is_hermitian (A * A) :=
is_hermitian_iff.mpr (by simp only [is_hermitian, adjoint_mul, is_hermitian_iff.mp h])

instance : has_coe (hermitian 𝕜 E) (operator 𝕜 E) := ⟨hermitian.operator⟩

instance : has_zero (hermitian 𝕜 E) := ⟨⟨0, is_hermitian_iff.mpr adjoint_zero⟩⟩

instance : has_one (hermitian 𝕜 E) := ⟨⟨1, is_hermitian_iff.mpr adjoint_one⟩⟩

lemma hermitian_adjoint (H : hermitian 𝕜 E) : (↑H : operator 𝕜 E)† = ↑H := is_hermitian_iff.mp H.self

instance : has_add (hermitian 𝕜 E) := ⟨λ A B, ⟨A + B, is_hermitian_iff.mpr (by simp only [adjoint_add, hermitian_adjoint])⟩⟩

instance : has_sub (hermitian 𝕜 E) := ⟨λ A B, ⟨A - B, is_hermitian_iff.mpr (by simp only [adjoint_sub, hermitian_adjoint])⟩⟩

instance : has_pow (hermitian 𝕜 E) ℕ := ⟨λ A n, ⟨power (↑A) n, is_hermitian_iff.mpr (by simp only [adjoint_power, hermitian_adjoint])⟩⟩

instance : has_scalar ℝ (hermitian 𝕜 E) :=
⟨λ r A, ⟨(↑r : 𝕜) • A, is_hermitian_iff.mpr (by simp only [adjoint_smul, conj_of_real, hermitian_adjoint])⟩⟩

lemma hermitian_inner (A : hermitian 𝕜 E) (x y : E) : ⟪x, A y⟫ = ⟪A x, y⟫ := A.self x y

lemma inner_self_real (A : hermitian 𝕜 E) (x : E) : ↑(re ⟪x, A x⟫) = ⟪x, A x⟫ := eq_conj_iff_re.mp
(by simp only [inner_conj_sym, hermitian_inner])

lemma hermitian_pow_def (A : hermitian 𝕜 E) (n : ℕ) : (↑(A^n) : operator 𝕜 E) = power A n := rfl

lemma hermitian_pow_two (A : hermitian 𝕜 E) : (↑(A^2) : operator 𝕜 E) = A * A := by simp only [hermitian_pow_def, power_two]

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

def eigenspace (A : operator 𝕜 E) (k : 𝕜) : submodule 𝕜 E := (A - lsmul 𝕜 𝕜 k).ker

lemma eigenspace_eq (A : operator 𝕜 E) (k : 𝕜) : eigenspace A k = module.End.eigenspace (A.to_linear_map) k := rfl

@[simp] lemma mem_eigenspace_iff {A : operator 𝕜 E} {k : 𝕜} {x} : x ∈ eigenspace A k ↔ A x = k • x :=
by rw [eigenspace, continuous_linear_map.mem_ker, continuous_linear_map.sub_apply,
  continuous_linear_map.lsmul_apply, sub_eq_zero]

instance (A : operator 𝕜 E) (k : 𝕜) : complete_space (eigenspace A k) :=
continuous_linear_map.complete_space_ker (A - lsmul 𝕜 𝕜 k)

def Projection (A : operator 𝕜 E) (k : 𝕜) : operator 𝕜 E := (subtype_val _).comp (orthogonal_projection (eigenspace A k))

-- Born規則
def density (A : operator 𝕜 E) (k : 𝕜) (ψ : E) : ℝ := ∥Projection A k ψ∥^2

-- 期待値
def expectation (A : operator 𝕜 E) (ψ : E) : ℝ := re ⟪ψ, A ψ⟫

-- ゆらぎ
def fluctuation (A : operator 𝕜 E) (ψ : E) : ℝ := let Δ := A - lsmul 𝕜 𝕜 ⟪ψ, A ψ⟫ in re ⟪ψ, (Δ * Δ) ψ⟫

section 
variables (A : operator 𝕜 E) (k : 𝕜) (ψ : E)

lemma Projection_eq_projection_fn : Projection A k ψ = orthogonal_projection_fn (eigenspace A k) ψ := rfl

lemma density_eq_re_inner : density A k ψ = re ⟪ψ, Projection A k ψ⟫ :=
have ⟪ψ - Projection A k ψ, Projection A k ψ⟫ = 0, from orthogonal_projection_fn_inner_eq_zero ψ _ (orthogonal_projection_fn_mem ψ), 
calc
  density A k ψ = re ⟪Projection A k ψ, Projection A k ψ⟫                                              : by rw [density, norm_sq_eq_inner]
            ... = re (⟪Projection A k ψ, Projection A k ψ⟫ + ⟪ψ - Projection A k ψ, Projection A k ψ⟫) : by rw [this, add_zero]
            ... = re ⟪ψ, Projection A k ψ⟫                                                             : by rw [←inner_add_left, add_sub_cancel'_right]

lemma fluctuation_eq_sub (nml : ∥ψ∥ = 1) : fluctuation A ψ = re (⟪ψ, (A * A) ψ⟫ - ⟪ψ, A ψ⟫^2) :=
have eq_pow2 : (lsmul 𝕜 𝕜 ⟪ψ, A ψ⟫ : E →L[𝕜] E) * (lsmul 𝕜 𝕜 ⟪ψ, A ψ⟫) = lsmul 𝕜 𝕜 (⟪ψ, A ψ⟫^2),
{ ext _, simp only [pow_two, mul_apply, lsmul_apply, smul_smul] },
have eq_smul : lsmul 𝕜 𝕜 ⟪ψ, A ψ⟫ * A = ⟪ψ, A ψ⟫ • A,
{ ext _, simp only [mul_apply, smul_apply, lsmul_apply] },
have eq_smul' : A * lsmul 𝕜 𝕜 ⟪ψ, A ψ⟫ = ⟪ψ, A ψ⟫ • A,
{ ext _, simp only [mul_apply, smul_apply, lsmul_apply, map_smul] },
have inner1 : ⟪ψ, ψ⟫ = 1,
{ simp only [inner_self_eq_norm_sq_to_K, nml, ←is_R_or_C.of_real_pow, one_pow,of_real_one] },
calc
  fluctuation A ψ = re (⟪ψ, ((A - lsmul 𝕜 𝕜 ⟪ψ, A ψ⟫) * (A - lsmul 𝕜 𝕜 ⟪ψ, A ψ⟫)) ψ⟫)            : rfl
              ... = re (⟪ψ, (A * A - ⟪ψ, A ψ⟫ • A - ⟪ψ, A ψ⟫ • A + lsmul 𝕜 𝕜 (⟪ψ, A ψ⟫^2)) ψ⟫)   : by simp only [sub_mul, mul_sub, eq_pow2, eq_smul, eq_smul', sub_add]
              ... = re (⟪ψ, (A * A) ψ⟫ - ⟪ψ, A ψ⟫ * ⟪ψ, A ψ⟫ - ⟪ψ, A ψ⟫ * ⟪ψ, A ψ⟫ + ⟪ψ, A ψ⟫^2) : by simp only [add_apply, sub_apply, inner_add_right, inner_sub_right,
                                                                                                   inner_smul_right, continuous_linear_map.smul_apply, lsmul_apply, inner1, mul_one]
              ... = re (⟪ψ, (A * A) ψ⟫ - ⟪ψ, A ψ⟫^2)                                             : by simp only [pow_two, sub_add_cancel]

end

def communitator (A B : operator 𝕜 E) : operator 𝕜 E := A * B - B * A

notation `[` A `; ` B `]` := communitator A B

def commute (A B : operator 𝕜 E) : Prop := A * B = B * A

end inner_product_space


