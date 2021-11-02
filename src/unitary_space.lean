import hilbert_space
import analysis.inner_product_space.pi_L2

noncomputable theory

open inner_product_space
open_locale classical

universes u v

variables (n : Type u) [fintype n]

-- n次元ユニタリ空間 ℂ^n
@[reducible] def unitary_space := pi_Lp 2 (λ i : n, ℂ)

local notation `ℂ^`:max n := unitary_space n

local notation `𝑖` := complex.I

instance : inner_product_space ℂ (ℂ^n) :=
pi_Lp.inner_product_space (λ i : n, ℂ)

instance : complete_space (ℂ^n) := complete_of_proper

instance : finite_dimensional ℂ (ℂ^n) := euclidean_space.finite_dimensional

instance : has_continuous_smul ℂ (ℂ^n) := has_bounded_smul.has_continuous_smul

instance : module ℂ (ℂ^n) := normed_space.to_module

def simple_basis : basis n ℂ (ℂ^n) := pi.basis_fun ℂ n

variables {n}

@[simp] lemma simple_basis_apply (i : n) (x : unitary_space n) : (simple_basis n).repr x i = x i := by simp[simple_basis]

def matrix.to_operator (M : matrix n n ℂ) (b : basis n ℂ (ℂ^n)) :
  operator ℂ (ℂ^n) := linear_map.to_continuous_linear_map (matrix.to_lin b b M)

@[simp] def matrix.to_operator' (M : matrix n n ℂ) :
  operator ℂ (ℂ^n) := linear_map.to_continuous_linear_map (matrix.to_lin' M)

namespace unitary_space
@[simp] def matrix22 (m₁₁ m₁₂ m₂₁ m₂₂ : ℂ) : matrix bool bool ℂ
| ff ff := m₁₁
| ff tt := m₁₂
| tt ff := m₂₁
| tt tt := m₂₂

@[simp] def vec2 (v₁ v₂ : ℂ) : ℂ^bool
| ff := v₁
| tt := v₂

local notation `[` b₁₁ `, ` b₁₂ `|` b₂₁ `, ` b₂₂ `]` := matrix22 b₁₁ b₁₂ b₂₁ b₂₂

def Pauli₀ : operator ℂ (ℂ^bool) := 1
def Pauli₁ : operator ℂ (ℂ^bool) := [0,  1 |  1,  0].to_operator'
def Pauli₂ : operator ℂ (ℂ^bool) := [0, -𝑖 | -𝑖,  0].to_operator'
def Pauli₃ : operator ℂ (ℂ^bool) := [1,  0 |  0, -1].to_operator'

lemma Pauli₁_hermitian : is_hermitian Pauli₁ :=
(λ x y, by {
  have : ∀ v, [0, 1|1, 0].mul_vec v = vec2 (v tt) (v ff), 
  { intros v, funext b, cases b; simp[matrix.mul_vec, matrix.dot_product] },
  simp[Pauli₁, this], exact add_comm _ _ })

lemma Pauli₂_hermitian : is_hermitian Pauli₂ :=
(λ x y, by {
  have : ∀ v, [0, -𝑖| -𝑖, 0].mul_vec v = -𝑖 • vec2 (v tt) (v ff), 
  { intros v, funext b, cases b; simp[matrix.mul_vec, matrix.dot_product] },
  simp[Pauli₂, this],
  })

end unitary_space
