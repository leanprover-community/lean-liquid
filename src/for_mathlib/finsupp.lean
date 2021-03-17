import data.finsupp.basic

noncomputable theory

open_locale big_operators

namespace finsupp

variables {α β M N : Type*} [add_comm_monoid M] [add_comm_monoid N]

@[simps]
def map_domain_hom (f : α → β) : (α →₀ M) →+ (β →₀ M) :=
{ to_fun := finsupp.map_domain f,
  map_zero' := finsupp.map_domain_zero,
  map_add' := λ _ _, finsupp.map_domain_add }

@[simps]
def map_range_hom (f : M →+ N) : (α →₀ M) →+ (α →₀ N) :=
{ to_fun := finsupp.map_range f f.map_zero,
  map_zero' := finsupp.map_range_zero,
  map_add' := finsupp.map_range_add f.map_add }

lemma map_range_hom_map_domain_hom (f : M →+ N) (g : α → β) :
  (map_range_hom f).comp (map_domain_hom g) =
  (map_domain_hom g).comp (map_range_hom f) :=
begin
  ext a m : 2,
  simp only [map_domain_single, map_range_single, add_monoid_hom.coe_comp,
    single_add_hom_apply, map_range_hom_apply, map_domain_hom_apply, function.comp_app]
end

lemma sum_eq_sum_fintype [fintype α] [has_zero β] (g : α → β → M) (h : ∀ a, g a 0 = 0)
  (f : α →₀ β) :
  f.sum g = ∑ a:α, g a (f a) :=
finset.sum_subset (finset.subset_univ _) $ λ a _ ha,
calc g a (f a) = g a 0 : congr_arg _ $ not_mem_support_iff.mp ha
... = 0 : h a

end finsupp
