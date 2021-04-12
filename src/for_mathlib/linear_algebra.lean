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

variables {m n o m' n' o' R : Type*}
variables [fintype m] [fintype n] [fintype o] [fintype m'] [fintype n'] [fintype o'] [semiring R]

lemma reindex_linear_equiv_mul_reindex_linear_equiv
  (e1 : m ≃ m') (e2 : n ≃ n') (e3 : o ≃ o') (M : matrix m n R) (M') :
  (reindex_linear_equiv e1 e2 M).mul (reindex_linear_equiv e2 e3 M') =
  reindex_linear_equiv e1 e3 (M.mul M') :=
begin
  ext i j,
  simp only [coe_reindex_linear_equiv, matrix.mul_apply],
  rw ← e2.sum_comp,
  simp only [equiv.symm_apply_apply],
end

end

end matrix


#lint- only unused_arguments def_lemma doc_blame
