import linear_algebra.matrix

namespace matrix
open equiv

section

variables {m n R : Type*} [fintype m] [fintype n] [semiring R] (M : matrix m n R)

lemma reindex_linear_equiv_sum_empty_symm :
  (reindex_linear_equiv (sum_empty _) (sum_empty _)).symm M = from_blocks M 0 0 0 :=
begin
  ext (i|i) (j|j),
  { simp only [sum_empty_apply_inl, reindex_linear_equiv_symm_apply, from_blocks_apply₁₁] },
  { cases j },
  { cases i }
end

end
.
section

variables {m n o m' n' o' m'' n'' R : Type*}
variables [fintype m] [fintype n] [fintype o] [fintype m'] [fintype n'] [fintype o']
variables [fintype m''] [fintype n'']
variables [semiring R]

lemma reindex_symm (e1 : m ≃ m') (e2 : n ≃ n') :
  (@reindex_linear_equiv _ _ _ _ _ _ _ _ R _ e1 e2).symm = reindex_linear_equiv e1.symm e2.symm :=
by { ext, dsimp, refl }

lemma reindex_trans
  (e1 : m ≃ m') (e2 : n ≃ n') (e1' : m' ≃ m'') (e2' : n' ≃ n'') :
  (reindex_linear_equiv e1 e2).trans (reindex_linear_equiv e1' e2') =
  @reindex_linear_equiv _ _ _ _ _ _ _ _ R _ (e1.trans e1') (e2.trans e2') :=
by { ext, dsimp, refl }

lemma reindex_reindex
  (e1 : m ≃ m') (e2 : n ≃ n') (e1' : m' ≃ m'') (e2' : n' ≃ n'') (M : matrix m n R) :
  (reindex_linear_equiv e1' e2') (reindex_linear_equiv e1 e2 M) =
  reindex_linear_equiv (e1.trans e1') (e2.trans e2') M :=
by { rw [← reindex_trans], refl }

end

end matrix


#lint- only unused_arguments def_lemma doc_blame
