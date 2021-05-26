import linear_algebra.matrix

namespace matrix
open equiv

section

variables {m n R : Type*} [fintype m] [fintype n] [semiring R] (M : matrix m n R)

lemma reindex_linear_equiv_sum_empty_symm (α β : Type*) [is_empty α] [is_empty β] :
  (reindex_linear_equiv (sum_empty _ α) (sum_empty _ β)).symm M = from_blocks M 0 0 0 :=
begin
  ext (i|i) (j|j),
  { simp only [reindex_linear_equiv_symm, from_blocks_apply₁₁], refl },
  { exact is_empty_elim j },
  { exact is_empty_elim i }
end

end
.
section

variables {m n o m' n' o' m'' n'' R : Type*}
variables [fintype m] [fintype n] [fintype o] [fintype m'] [fintype n'] [fintype o']
variables [fintype m''] [fintype n'']
variables [semiring R]

lemma reindex_linear_equiv_trans (e1 : m ≃ m') (e2 : n ≃ n') (e1' : m' ≃ m'') (e2' : n' ≃ n'') :
  (reindex_linear_equiv e1 e2).trans (reindex_linear_equiv e1' e2') =
  @reindex_linear_equiv _ _ _ _ _ _ _ _ R _ (e1.trans e1') (e2.trans e2') :=
by { ext, dsimp, refl }

lemma reindex_reindex (e1 : m ≃ m') (e2 : n ≃ n') (e1' : m' ≃ m'') (e2' : n' ≃ n'')
  (M : matrix m n R) :
  (reindex_linear_equiv e1' e2') (reindex_linear_equiv e1 e2 M) =
  reindex_linear_equiv (e1.trans e1') (e2.trans e2') M :=
by { rw [← reindex_linear_equiv_trans], refl }

@[simp] lemma reindex_linear_equiv_one [decidable_eq m] [decidable_eq m'] (e1 : m ≃ m') :
  (reindex_linear_equiv e1 e1 (1 : matrix m m R)) = 1 :=
begin
  ext i j,
  dsimp only [reindex_linear_equiv_apply, reindex_apply, minor_apply, one_apply],
  simp only [eq_self_iff_true, apply_eq_iff_eq],
  convert rfl
end

lemma mul_reindex_linear_equiv_one [decidable_eq o] (e1 : o ≃ n) (e2 : o ≃ n') (M : matrix m n R) :
  M.mul (reindex_linear_equiv e1 e2 1) = reindex_linear_equiv (equiv.refl _) (e1.symm.trans e2) M :=
begin
  have : M = reindex_linear_equiv (equiv.refl _) e1 (reindex_linear_equiv (equiv.refl _) e1.symm M),
  { rw [reindex_reindex, equiv.symm_trans, equiv.refl_trans, reindex_linear_equiv_refl_refl], refl },
  conv_lhs { rw this },
  rw [← reindex_linear_equiv_mul, matrix.mul_one, reindex_reindex, equiv.refl_trans]
end

end

end matrix


#lint- only unused_arguments def_lemma doc_blame
