import hilbert_space
import data.equiv.ring
import algebra.big_operators.ring
import measure_theory.function.l2_space

notation `L²[`:25 E `, ` μ `]` := measure_theory.Lp E 2 μ

noncomputable instance {α : Type*} {E : Type*} {𝕜 : Type*} [is_R_or_C 𝕜] [measurable_space α]
  {μ : measure_theory.measure α} [measurable_space E] [inner_product_space 𝕜 E] [borel_space E] [complete_space E]
  [topological_space.second_countable_topology E] [measurable_space 𝕜] [borel_space 𝕜] :
  hilbert_space 𝕜 L²[E, μ] :=
{ inner := measure_theory.L2.inner_product_space,
  complete := @measure_theory.Lp.complete_space _ _ _ 2 _ _ _ _ _ _ fact_one_le_two_ennreal }