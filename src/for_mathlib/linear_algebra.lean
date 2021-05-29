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

lemma reindex_linear_equiv_trans (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'') (e₂' : n' ≃ n'') :
  (reindex_linear_equiv e₁ e₂).trans (reindex_linear_equiv e₁' e₂') =
    @reindex_linear_equiv _ _ _ _ _ _ _ _ R _ (e₁.trans e₁') (e₂.trans e₂') :=
by { ext, refl }

lemma reindex_linear_equiv_reindex_linear_equiv
  (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'') (e₂' : n' ≃ n'') (M : matrix m n R) :
  (reindex_linear_equiv e₁' e₂') (reindex_linear_equiv e₁ e₂ M) =
    reindex_linear_equiv (e₁.trans e₁') (e₂.trans e₂') M :=
by { rw [← reindex_linear_equiv_trans], refl }

@[simp] lemma reindex_linear_equiv_one [decidable_eq m] [decidable_eq m'] (e : m ≃ m') :
  (reindex_linear_equiv e e (1 : matrix m m R)) = 1 :=
begin
  ext i j,
  dsimp only [reindex_linear_equiv_apply, reindex_apply, minor_apply, one_apply],
  simp only [eq_self_iff_true, apply_eq_iff_eq],
  convert rfl
end

lemma mul_reindex_linear_equiv_one [decidable_eq o] (e₁ : o ≃ n) (e₂ : o ≃ n') (M : matrix m n R) :
  M.mul (reindex_linear_equiv e₁ e₂ 1) = reindex_linear_equiv (equiv.refl _) (e₁.symm.trans e₂) M :=
begin
  have : M = reindex_linear_equiv (equiv.refl _) e₁ (reindex_linear_equiv (equiv.refl _) e₁.symm M),
  { rw [reindex_linear_equiv_reindex_linear_equiv, equiv.symm_trans, equiv.refl_trans,
      reindex_linear_equiv_refl_refl],
    refl },
  conv_lhs { rw this },
  rw [← reindex_linear_equiv_mul, matrix.mul_one, reindex_linear_equiv_reindex_linear_equiv,
    equiv.refl_trans]
end

end

end matrix


#lint- only unused_arguments def_lemma doc_blame
