import algebra.ring
import algebra.algebra.basic
import algebra.star.basic
import data.complex.is_R_or_C


universes u v
variables (đ : Type u) (A : Type v)
  [is_R_or_C đ] [semiring A] [star_ring A] [algebra đ A] [normed_ring A] 

postfix `â`:max := star

class C_star_algebra :=
(C_star_property : â a : A, âĽaâ * aâĽ = âĽaâĽ^2)