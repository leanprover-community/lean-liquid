import algebra.group.hom
import algebra.big_operators

open_locale big_operators

namespace add_monoid_hom

variables {M₁ M₂ : Type*}

section
variables [add_monoid M₁] [add_comm_monoid M₂]

@[simp] lemma sum_apply {ι : Type*} (s : finset ι) (f : ι → (M₁ →+ M₂)) (m : M₁) :
  (∑ i in s, f i) m = ∑ i in s, (f i m) :=
begin
  classical,
  apply finset.induction_on s,
  { simp only [finset.sum_empty, zero_apply] },
  { intros i s his IH, simp only [his, IH, finset.sum_insert, not_false_iff, add_apply] }
end

end

section
variables [add_monoid M₁] [add_comm_group M₂]

@[simp] lemma gsmul_apply (n : ℤ) (f : (M₁ →+ M₂)) (m : M₁) :
  (n •ℤ f) m = n •ℤ (f m) :=
show eval m (n •ℤ f) = n •ℤ eval m f, from add_monoid_hom.map_gsmul _ _ _

end

end add_monoid_hom
#lint- only unused_arguments def_lemma doc_blame
