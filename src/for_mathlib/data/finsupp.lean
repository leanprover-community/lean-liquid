

namespace finsupp
variables {α α' M R : Type*} [semiring R] [add_comm_monoid M] [module R M]

lemma finsupp.total_comap_domain' (v : α' → M) (f : α → α') (l : α' →₀ R)
  (hf : set.inj_on f (f ⁻¹' ↑l.support)) (hsupp : (l.support : set α') ⊆ set.range f) :
  finsupp.total α M R (v ∘ f) (l.comap_domain f hf) = ∑ i in l.support, l i • v i :=
begin
  haveI := classical.dec_eq α',
  rw finsupp.total_apply,
  simp [finsupp.sum, finsupp.comap_domain],
  exact finset.sum_comap l.support f (λ x, l x • v x) hf hsupp
end

end finsupp
