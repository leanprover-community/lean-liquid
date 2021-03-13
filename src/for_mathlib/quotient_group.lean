import group_theory.quotient_group


namespace add_subgroup
variables {M : Type*} [add_group M]

lemma exists_mem_iff_exists_neg_mem  (S : add_subgroup M) {P : M → Prop} :
  (∃ x ∈ S, P x) ↔ ∃ x ∈ S, P (-x) :=
by split ; rintros ⟨x, x_in, hx⟩ ; exact ⟨-x, neg_mem S x_in, by simp [hx]⟩

end add_subgroup

namespace quotient_add_group
variables {M : Type*} [add_comm_group M]

lemma mk'_eq_mk'_iff {S : add_subgroup M} {x y : M} :  mk' S x = mk' S y ↔  x - y ∈ S :=
begin
  change ↑x = ↑ y ↔ _,
  rw [quotient_add_group.eq, ← S.neg_mem_iff],
  simp [add_comm, sub_eq_add_neg],
end

lemma mk'_eq_zero_iff {S : add_subgroup M} {x : M} :  mk' S x = 0 ↔  x ∈ S :=
by erw [mk'_eq_mk'_iff, sub_zero]

end quotient_add_group
