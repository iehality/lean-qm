import hilbert_space
import analysis.inner_product_space.pi_L2

noncomputable instance : hilbert_space ℂ ℂ :=
{inner := is_R_or_C.inner_product_space, complete := complete_of_proper}

-- n次元ユニタリ空間 ℂ^n
@[reducible] def C_vec (n : Type*) [fintype n] := pi_Lp 2 one_le_two (λ i : n, ℂ)

noncomputable instance (n : Type*) [fintype n] : hilbert_space ℂ (C_vec n) :=
{ inner := pi_Lp.inner_product_space (λ i : n, ℂ), complete := complete_of_proper, }
