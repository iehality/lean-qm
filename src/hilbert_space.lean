import analysis.inner_product_space.basic
import analysis.inner_product_space.projection
import analysis.normed_space.dual
import data.real.nnreal
import order.filter.ultrafilter
import order.filter.partial
import algebra.support
universes u v

noncomputable theory
open_locale classical

def nhdsf {α} [topological_space α]  (a : α) : filter α := (⨅ s ∈ {s : set α | a ∈ s ∧ is_open s}, filter.principal s)

namespace inner_product_space
open is_R_or_C continuous_linear_map
variables  {𝕜 : Type u} [is_R_or_C 𝕜] {E : Type v} [inner_product_space 𝕜 E]

@[reducible] def operator (𝕜 : Type u) [is_R_or_C 𝕜] (E : Type v) [inner_product_space 𝕜 E] := E →ₗ[𝕜] E
local notation `⟪`x`, `y`⟫` := @inner 𝕜 E _ x y

def adjoint (A B : operator 𝕜 E) : Prop := ∀ φ ψ : E, ⟪A φ, ψ⟫ = ⟪φ, B ψ⟫
local infix ` † `:15 := adjoint

def hermitian (A : operator 𝕜 E) : Prop := A † A

lemma adjoint.add {A A' B B' : operator 𝕜 E} (h : A † B) (h' : A' † B') : A + A' † B + B' := λ φ ψ,
calc ⟪A φ + A' φ, ψ⟫ = ⟪A φ, ψ⟫ + ⟪A' φ, ψ⟫ : by simp only [inner_add_left]
                 ... = ⟪φ, B ψ⟫ + ⟪φ, B' ψ⟫ : by rw [h, h']
                 ... = ⟪φ, B ψ + B' ψ⟫      : by simp only [inner_add_right]

lemma adjoint.mul {A A' B B' : operator 𝕜 E} (h : A † B) (h' : A' † B') : A * A' † B' * B := λ φ ψ,
calc ⟪A (A' φ), ψ⟫ = ⟪A' φ, B ψ⟫   : by rw h
               ... = ⟪φ, B' (B ψ)⟫ : by rw h'

lemma adjoint.symm {A B : operator 𝕜 E} (h : B † A) : A † B := λ φ ψ,
calc ⟪A φ, ψ⟫ = conj ⟪ψ, A φ⟫ : by simp
          ... = conj ⟪B ψ, φ⟫ : by rw h
          ... = ⟪φ, B ψ⟫      : by simp

lemma adjoint.scalar_left {A B : operator 𝕜 E} (h : A † B) (c : 𝕜) : c • A † (conj c) • B := λ φ ψ,
calc ⟪c • A φ, ψ⟫ = conj c * ⟪A φ, ψ⟫   : by simp only [inner_smul_left]
              ... = conj c * ⟪φ, B ψ⟫   : by rw h
              ... = ⟪φ, conj c • (B ψ)⟫ : by simp only [inner_smul_right]

lemma adjoint.scalar_real {E : Type v} [inner_product_space ℂ E]
  {A B : operator ℂ E} (h : A † B) (r : ℝ) : r • A † r • B :=
by { have := h.scalar_left r, simp at this, exact this }

lemma hermitial.add {A B : operator 𝕜 E} (hA : hermitian A) (hB : hermitian B) :
  hermitian (A + B) := adjoint.add hA hB

lemma hermitial.scalar_real {E : Type v} [inner_product_space ℂ E]
  {A : operator ℂ E} (h : hermitian A) (r : ℝ) :
  hermitian (r • A) := adjoint.scalar_real h r

def bra (φ : E) : E →ₗ[𝕜] 𝕜 :=
{to_fun := inner φ, map_add' := λ x y, inner_add_right, map_smul' := λ x y, inner_smul_right}

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

variable [i : inner_product_space 𝕜 E]
include i

def distance (φ : E) (D : set E) : ℝ := Inf {r | ∃ ψ ∈ D, r = ∥φ - ψ∥}



end inner_product_space

class hilbert_space (𝕜 : Type*) [is_R_or_C 𝕜] (E : Type*) :=
(inner : inner_product_space 𝕜 E)
(complete : complete_space E)

namespace hilbert_space
open is_R_or_C
open_locale big_operators classical topological_space

variables {𝕜 : Type u} [is_R_or_C 𝕜] {E : Type v} [hilbert_space 𝕜 E]

noncomputable instance : inner_product_space 𝕜 E := hilbert_space.inner

local notation `⟪`x`, `y`⟫` := @inner 𝕜 E _ x y

structure complete_orthonormal (ι : Type*) (𝕜 : Type u) [is_R_or_C 𝕜] (E : Type v) [hilbert_space 𝕜 E] :=
(repr : ι → E)
(orthonormal : orthonormal 𝕜 repr)

end hilbert_space


