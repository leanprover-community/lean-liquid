import linear_algebra.matrix

/-!
# Kronecker product of matrices

TODO: this should probably become a bilinear map
we might want to vary coefficient rings

-/

open_locale big_operators

namespace matrix

variables {m n o m' n' o' R: Type*}
variables [fintype m] [fintype n] [fintype o] [fintype m'] [fintype n'] [fintype o']

def kronecker [has_mul R] (f : matrix m n R) (f' : matrix m' n' R) :
  matrix (m × m') (n × n') R :=
λ i j, f i.1 j.1 * f' i.2 j.2

lemma kronecker_mul [decidable_eq n'] [comm_semiring R]
  (f : matrix m n R) (g : matrix n o R) (f' : matrix m' n' R) (g' : matrix n' o' R) :
  (f.mul g).kronecker (f'.mul g') =
    (f.kronecker f').mul (g.kronecker g') :=
begin
  ext ⟨i, i'⟩ ⟨j, j'⟩,
  dsimp [mul_apply, kronecker],
  simp only [finset.sum_mul, finset.mul_sum],
  rw [← finset.univ_product_univ, finset.sum_product, finset.sum_comm],
  simp only [mul_assoc, mul_left_comm (g _ j)],
end

lemma kronecker_one_one [decidable_eq m] [decidable_eq n] [semiring R] :
  kronecker (1 : matrix m m R) (1 : matrix n n R) = 1 :=
begin
  ext ⟨i, i'⟩ ⟨j, j'⟩,
  simp only [kronecker, one_apply, boole_mul, prod.mk.inj_iff],
  convert (@ite_and _ (i = j) (i' = j') _ _ (1 : R) (0 : R)).symm
end

end matrix
