import hilbert_space

universes u v

noncomputable theory

theorem real.sq_le_sq_of_le {x y : ℝ} (h : |x| ≤ |y|) : x^2 ≤ y^2 :=
(real.sq_le (sq_nonneg y)).mpr (by { simp only [real.sqrt_sq_eq_abs y], exact abs_le.mp h })

theorem real.sq_le_sq_of_le' {x y : ℝ} (h : |x| ≤ y) : x^2 ≤ y^2 :=
real.sq_le_sq_of_le (le_abs.mpr (or.inl h))

namespace inner_product_space
open is_R_or_C continuous_linear_map

variables {𝕜 : Type u} [is_R_or_C 𝕜] {E : Type v} [inner_product_space 𝕜 E] [complete_space E]

local notation `⋆` := (star_ring_aut : ring_aut 𝕜)

local notation `⟪`x`, `y`⟫` := @inner 𝕜 E _ x y

local notation `〈` x `|`:= inner_right x

local notation `𝑖` := @is_R_or_C.I 𝕜 _

-- Born規則
def density (ψ : E) (A : hermitian 𝕜 E) (k : 𝕜) : ℝ := ∥Projection ↑A k ψ∥^2

-- 期待値
def expectation (ψ : E) (A : hermitian 𝕜 E): ℝ := re ⟪ψ, A ψ⟫

-- ゆらぎ
def fluctuation (ψ : E) (A : hermitian 𝕜 E) : ℝ := let Δ := A - expectation ψ A • 1 in re ⟪ψ, (Δ^2) ψ⟫

notation `Δ²[` ψ `]` := fluctuation ψ

section 
variables (A : hermitian 𝕜 E) (k : 𝕜) (ψ : E)

lemma expectation_eq : ↑(expectation ψ A) = ⟪ψ, A ψ⟫ := hermitian.inner_real A ψ

lemma fluctuation_eq : ↑(Δ²[ψ] A) = let Δ := A - expectation ψ A • 1 in ⟪ψ, (Δ^2) ψ⟫ := hermitian.inner_real _ _

lemma density_eq_re_inner : density ψ A k = re ⟪ψ, Projection ↑A k ψ⟫ :=
have ⟪ψ - Projection ↑A k ψ, Projection ↑A k ψ⟫ = 0, from orthogonal_projection_fn_inner_eq_zero ψ _ (orthogonal_projection_fn_mem ψ), 
calc
  density ψ A k = re ⟪Projection ↑A k ψ, Projection ↑A k ψ⟫                                                  : by rw [density, norm_sq_eq_inner]
            ... = re (⟪Projection ↑A k ψ, Projection ↑A k ψ⟫ + ⟪ψ - Projection ↑A k ψ, Projection ↑A k ψ⟫) : by rw [this, add_zero]
            ... = re ⟪ψ, Projection ↑A k ψ⟫                                                                   : by rw [←inner_add_left, add_sub_cancel'_right]

lemma fluctuation_eq_sub (nml : ∥ψ∥ = 1) : ↑(Δ²[ψ] A) = ⟪ψ, (A^2) ψ⟫ - ⟪ψ, A ψ⟫^2 :=
have eq_pow2 : (⟪ψ, A ψ⟫ • 1 : E →L[𝕜] E) * (⟪ψ, A ψ⟫ • 1) = ⟪ψ, A ψ⟫^2 • 1,
{ ext _, simp only [pow_two, mul_apply, smul_apply, one_apply, smul_smul] },
have eq_smul : ∀ k : 𝕜, (k • 1 : operator 𝕜 E) * A = k • A,
{ intros k, ext _, simp only [mul_apply, smul_apply, one_apply] },
have eq_smul' : ∀ k : 𝕜, (A : operator 𝕜 E) * (k • 1) = k • A,
{ intros k, ext _, simp only [mul_apply, smul_apply, one_apply, map_smul] },
have inner1 : ⟪ψ, ψ⟫ = 1,
{ simp only [inner_self_eq_norm_sq_to_K, nml, ←is_R_or_C.of_real_pow, one_pow,of_real_one] },
calc ↑(Δ²[ψ] A) = ⟪ψ, ((A - expectation ψ A • 1)^2) ψ⟫
  : by rw fluctuation_eq
           ... = ⟪ψ, ((A - ⟪ψ, A ψ⟫ • 1 : operator 𝕜 E) * (A - ⟪ψ, A ψ⟫ • 1)) ψ⟫
  : by simp only [expectation_eq A ψ, ←hermitian.apply, hermitian.pow_two, hermitian.sub_coe, hermitian.smul_coe, hermitian.one_coe]
           ... = ⟪ψ, ((A : operator 𝕜 E) * A - ⟪ψ, A ψ⟫ • A - ⟪ψ, A ψ⟫ • A + ⟪ψ, A ψ⟫^2 • 1) ψ⟫
  : by simp only [sub_mul, mul_sub, eq_pow2, sub_add, eq_smul, eq_smul']
           ... = ⟪ψ, (A^2) ψ⟫ - ⟪ψ, A ψ⟫ * ⟪ψ, A ψ⟫ - ⟪ψ, A ψ⟫ * ⟪ψ, A ψ⟫ + ⟪ψ, A ψ⟫^2
  : by simp only [add_apply, sub_apply, inner_add_right, inner_sub_right, inner_smul_right, smul_apply, one_apply,
                  inner1, mul_one, hermitian.apply, ←hermitian.pow_two]
           ... = ⟪ψ, (A^2) ψ⟫ - ⟪ψ, A ψ⟫^2
  : by simp only [pow_two, sub_add_cancel]

def diff (A : hermitian 𝕜 E) (ψ : E) : hermitian 𝕜 E := A - expectation ψ A • 1 

lemma fluctuation_eq_norm_sq : Δ²[ψ] A = ∥diff A ψ ψ∥^2 :=
let Δ : hermitian 𝕜 E := A - expectation ψ A • 1 in
calc Δ²[ψ] A = re ⟪ψ, Δ (Δ ψ)⟫ : by simp only [Δ, fluctuation, hermitian.apply_pow_two, mul_apply, hermitian.apply]
         ... = re ⟪Δ ψ, Δ ψ⟫   : by rw hermitian.inner_comm
         ... = ∥Δ ψ∥^2         : by rw norm_sq_eq_inner

end

theorem fluctuation_lower_bound (A B : hermitian 𝕜 E) (ψ : E) :
  (re ⟪ψ, -𝑖⟦A, B⟧ ψ⟫)^2 / 4 ≤ Δ²[ψ] A * Δ²[ψ] B :=
let ΔA : hermitian 𝕜 E := diff A ψ,
    ΔB : hermitian 𝕜 E := diff B ψ in
have div_eq : ∀ z : 𝕜, re (z / 2) = re z / 2,
{ intros z, have := @div_re_of_real _ _ z 2, simp at this, exact this },
have comt_eq: -𝑖⟦ΔA, ΔB⟧ = -𝑖⟦A, B⟧,
{ refine hermitian.ext' _,
  simp only [communitator_hermitian_eq, ΔA, ΔB, diff, hermitian.sub_coe, hermitian.smul_coe, hermitian.one_coe,
  communitator.sub_left, communitator.sub_right, communitator.smul_left, communitator.smul_right,
  communitator.one_left, communitator.one_right, smul_zero, sub_zero]  },
calc (re ⟪ψ, -𝑖⟦A, B⟧ ψ⟫)^2 / 4 = (re (⟪ψ, -𝑖⟦ΔA, ΔB⟧ ψ⟫ / 2))^2                      : by rw comt_eq; simp only [div_eq, div_pow]; ring
                            ... = (re (𝑖 * (⟪ψ, ΔB (ΔA ψ)⟫ - ⟪ψ, ΔA (ΔB ψ)⟫) / 2))^2  : by simp only [communitator_hermitian.apply, sub_apply, smul_apply, mul_apply,
                                                                                           hermitian.apply, inner_sub_right, mul_sub, inner_smul_right]
                            ... = (re (𝑖 * (⋆⟪ψ, ΔA (ΔB ψ)⟫ - ⟪ψ, ΔA (ΔB ψ)⟫) / 2))^2 : by simp only [inner_conj_sym, hermitian.inner_comm]
                            ... = (im ⟪ΔA ψ, ΔB ψ⟫)^2                                 : by simp only [←im_eq_conj_sub, of_real_re, hermitian.inner_comm]
                            ... ≤ (abs ⟪ΔA ψ, ΔB ψ⟫)^2                                : real.sq_le_sq_of_le' (abs_im_le_abs ⟪ΔA ψ, ΔB ψ⟫)
                            ... ≤ (∥ΔA ψ∥ * ∥ΔB ψ∥)^2                                 : real.sq_le_sq_of_le' (by simp only [abs_abs ⟪ΔA ψ, ΔB ψ⟫]; exact abs_inner_le_norm _ _)
                            ... = Δ²[ψ] A * Δ²[ψ] B                                   : by simp only [mul_pow, fluctuation_eq_norm_sq]

end inner_product_space