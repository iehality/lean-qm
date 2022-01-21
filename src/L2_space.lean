import hilbert_space
import data.equiv.ring
import algebra.big_operators.ring
import analysis.normed_space.lp_space
import analysis.inner_product_space.l2_space

universes u v

noncomputable theory
open_locale nnreal ennreal big_operators

variables
  {𝕜 : Type*} [is_R_or_C 𝕜] 
  {ι : Type*} {G : ι → Type*}
  [Π (i : ι), normed_group (G i)]
  [Π (i : ι), normed_space 𝕜 (G i)]
  [∀ (a : ι), complete_space (G a)]
  [Π (i : ι), inner_product_space 𝕜 (G i)]

notation `ℓ² ` G := lp G 2

namespace l2_space

instance : normed_group (ℓ² G) := have _ := fact_one_le_two_ennreal, by exactI lp.normed_group

instance : normed_space 𝕜 (ℓ² G) := have _ := fact_one_le_two_ennreal, by exactI lp.normed_space 

instance : complete_space (ℓ² G) := have _ := fact_one_le_two_ennreal, by exactI lp.complete_space





end l2_space