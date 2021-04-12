import linear_algebra.matrix

/-!
# Kronecker product of matrices

TODO: this should probably become a bilinear map
we might want to vary coefficient rings

-/

open_locale big_operators

namespace matrix

variables {m n o m' n' R: Type*}
variables [fintype n] [fintype m] [fintype o] [fintype n'] [fintype m']

def kronecker [has_mul R] (f : matrix m n R) (f' : matrix m' n' R) :
  matrix (m × m') (n × n') R :=
λ i j, f i.1 j.1 * f' i.2 j.2

lemma kronecker_mul [decidable_eq n'] [semiring R] (f : matrix m n R) (g : matrix n o R) :
  (f.mul g).kronecker (1 : matrix n' n' R) =
    (f.kronecker (1 : matrix n' n' R)).mul (g.kronecker 1) :=
begin
  ext ⟨i, i'⟩ ⟨j, j'⟩,
  dsimp [mul_apply, kronecker],
  rw [← finset.univ_product_univ, finset.sum_product, finset.sum_comm,
    finset.sum_eq_single j'],
  { simp only [one_apply, if_pos rfl, mul_one, finset.sum_mul],
    split_ifs; simp only [mul_one, mul_zero, zero_mul] },
  { rintro x - hx,
    simp only [one_apply_ne hx, mul_zero, finset.sum_const_zero] },
  { intro h, exact (h $ finset.mem_univ _).elim }
end


end matrix
