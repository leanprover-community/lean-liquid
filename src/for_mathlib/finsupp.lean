-- import data.finsupp.basic

-- noncomputable theory

-- open_locale big_operators

-- namespace finsupp

-- variables {α β M N : Type*} [add_comm_monoid M] [add_comm_monoid N]

-- lemma sum_eq_sum_fintype [fintype α] [has_zero β] (g : α → β → M) (h : ∀ a, g a 0 = 0)
--   (f : α →₀ β) :
--   f.sum g = ∑ a:α, g a (f a) :=
-- finset.sum_subset (finset.subset_univ _) $ λ a _ ha,
--   calc g a (f a) = g a 0 : congr_arg _ $ not_mem_support_iff.mp ha
--   ... = 0 : h a

-- end finsupp
