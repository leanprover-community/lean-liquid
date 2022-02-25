import Lbar.finsupp_instance

open finset finsupp
open_locale big_operators

section families_of_add_comm_groups

variables {S : Fintype} {α β : Type*}

--  Not needed anymore: the `semi_normed_group` instance has been removed
lemma sum_nnnorm_add_le [semi_normed_group α] (F G : S → α) :
  ∥F + G∥₊ ≤ ∥F∥₊ + ∥G∥₊ :=
show ∑ s, ∥F s + G s∥₊ ≤ ∑ s, ∥F s∥₊ + ∑ s, ∥G s∥₊, from
le_trans (sum_le_sum (λ i hi, nnnorm_add_le _ _)) univ.sum_add.le

--  Not needed anymore: this was a helper lemma for the triangle inequality
lemma add_zero_dists [decidable_eq α] [add_zero_class β] {l : α} {x y z : α →₀ β}
  (h : x l + y l + z l = 0) (hl : l ∈ x.support) :
  l ∈ y.support ∪ z.support :=
begin
  simp only [mem_support_iff, ne.def, mem_union] at hl ⊢,
  contrapose! hl,
  simpa only [hl, add_zero] using h,
end

--  Not needed anymore: this was a helper lemma for the triangle inequality
lemma dists [decidable_eq α] [add_group β] {l : α} {x y z : α →₀ β} (hl : l ∈ (x - z).support) :
  l ∈ (x - y).support ∪ (y - z).support :=
have xz : l ∈ (- (x - z)).support, by rwa support_neg,
add_zero_dists (by simp only [neg_sub, coe_sub, pi.sub_apply, sub_add_sub_cancel, sub_self]) xz

end families_of_add_comm_groups
