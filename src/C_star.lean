import algebra.ring
import algebra.algebra.basic
import algebra.star.basic
import data.complex.is_R_or_C


universes u v
variables (𝕜 : Type u) (A : Type v)
  [is_R_or_C 𝕜] [semiring A] [star_ring A] [algebra 𝕜 A] [normed_ring A] 

postfix `⋆`:max := star

class C_star_algebra :=
(C_star_property : ∀ a : A, ∥a⋆ * a∥ = ∥a∥^2)