import linear_algebra.matrix

namespace matrix
open equiv

variables {m n R : Type*} [fintype m] [fintype n] [semiring R] (M : matrix m n R)

lemma reindex_linear_equiv_sum_empty_symm :
  (reindex_linear_equiv (sum_empty _) (sum_empty _)).symm M = from_blocks M 0 0 0 :=
begin
  ext (i|i) (j|j),
  { simp only [sum_empty_apply_inl, reindex_linear_equiv_symm_apply, from_blocks_apply₁₁] },
  { cases j },
  { cases i }
end

end matrix
#lint- only unused_arguments def_lemma
