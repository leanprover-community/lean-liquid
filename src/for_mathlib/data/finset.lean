import algebra.big_operators.basic

open_locale big_operators

section finset

variables {β α α' : Type*}  [comm_monoid β]

@[simp, to_additive]
lemma finset.prod_preimage (s : finset α') (e : α → α') (f : α' → β) (he : set.inj_on e (e ⁻¹' ↑s))
  (hs : (s : set α') ⊆ set.range e) :
  ∏ x in s.preimage e he, f (e x) = ∏ x in s, f x :=
begin
  classical,
  rw [←finset.prod_image, finset.image_preimage, s.filter_eq_self.2 hs],
  simp_rw finset.mem_preimage,
  exact he,
end

end finset
