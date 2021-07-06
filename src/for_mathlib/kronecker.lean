import linear_algebra.matrix

/-!
# Kronecker product of matrices

TODO: this should probably become a bilinear map
we might want to vary coefficient rings

-/

open_locale big_operators

namespace matrix

variables {l m n o l' m' n' o' R: Type*}
variables [fintype l] [fintype m] [fintype n] [fintype o]
variables [fintype l'] [fintype m'] [fintype n'] [fintype o']


def kronecker [has_mul R] (f : matrix m n R) (f' : matrix m' n' R) :
  matrix (m × m') (n × n') R :=
λ i j, f i.1 j.1 * f' i.2 j.2

@[simps]
def kroneckerₗ [comm_semiring R] :
  matrix m n R →ₗ[R] matrix m' n' R →ₗ[R] matrix (m × m') (n × n') R :=
{ to_fun := λ M,
  { to_fun := λ M', M.kronecker M',
    map_add' := λ M'₁ M'₂, by { ext, apply mul_add },
    map_smul' := λ c M', by { ext, dsimp [kronecker], rw mul_left_comm } },
  map_add' := λ M₁ M₂, by { ext, apply add_mul },
  map_smul' := λ c M, by { ext, dsimp [kronecker], rw mul_assoc } }

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

@[simp] lemma kronecker_one_one [decidable_eq m] [decidable_eq n] [semiring R] :
  kronecker (1 : matrix m m R) (1 : matrix n n R) = 1 :=
begin
  ext ⟨i, i'⟩ ⟨j, j'⟩,
  simp only [kronecker, one_apply, boole_mul, prod.mk.inj_iff],
  convert (@ite_and _ (i = j) (i' = j') _ _ (1 : R) (0 : R)).symm
end
.

lemma kronecker_reindex [semiring R] (el : l ≃ l') (em : m ≃ m') (en : n ≃ n') (eo : o ≃ o')
  (M : matrix l m R) (N : matrix n o R) :
  kronecker (reindex_linear_equiv ℕ _ el em M) (reindex_linear_equiv ℕ _ en eo N) =
  reindex_linear_equiv ℕ _
    (el.prod_congr en) (em.prod_congr eo) (kronecker M N) :=
by { ext ⟨i, i'⟩ ⟨j, j'⟩, refl }

lemma kronecker_reindex_left [semiring R] (el : l ≃ l') (em : m ≃ m') (M : matrix l m R) (N : matrix n o R) :
  kronecker (reindex_linear_equiv ℕ _ el em M) N =
  reindex_linear_equiv ℕ _
    (el.prod_congr (equiv.refl _)) (em.prod_congr (equiv.refl _)) (kronecker M N) :=
by { ext ⟨i, i'⟩ ⟨j, j'⟩, refl }

lemma kronecker_reindex_right [semiring R] (en : n ≃ n') (eo : o ≃ o') (M : matrix l m R) (N : matrix n o R) :
  kronecker M (reindex_linear_equiv ℕ _ en eo N) =
  reindex_linear_equiv ℕ _
    ((equiv.refl _).prod_congr en) ((equiv.refl _).prod_congr eo) (kronecker M N) :=
by { ext ⟨i, i'⟩ ⟨j, j'⟩, refl }

lemma kronecker_assoc [semiring R] (A : matrix m m' R) (B : matrix n n' R) (C : matrix o o' R) :
  (A.kronecker B).kronecker C =
  reindex_linear_equiv ℕ _
    (equiv.prod_assoc _ _ _).symm
    (equiv.prod_assoc _ _ _).symm
    (A.kronecker (kronecker B C)) :=
by { ext ⟨⟨i, j⟩, k⟩ ⟨⟨i', j'⟩, k'⟩, apply mul_assoc }

lemma kronecker_assoc' [semiring R] (A : matrix m m' R) (B : matrix n n' R) (C : matrix o o' R) :
  A.kronecker (kronecker B C) =
  reindex_linear_equiv ℕ _
    (equiv.prod_assoc _ _ _)
    (equiv.prod_assoc _ _ _)
    ((A.kronecker B).kronecker C) :=
by { ext ⟨i, ⟨j, k⟩⟩ ⟨i', ⟨j', k'⟩⟩, symmetry, apply mul_assoc }

end matrix
