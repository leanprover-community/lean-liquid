import analysis.normed_space.basic

import for_mathlib.topology

open_locale nnreal big_operators

section

variables (G : Type*) [topological_space G] [group G] [topological_group G]

-- PRed in #6669
@[to_additive]
lemma discrete_topology_of_open_singleton_one (h : is_open ({1} : set G)) : discrete_topology G :=
begin
  rw ← singletons_open_iff_discrete,
  intro g,
  suffices : {g} = (λ (x : G), g⁻¹ * x) ⁻¹' {1},
  { rw this, exact (continuous_mul_left (g⁻¹)).is_open_preimage _ h, },
  simp only [mul_one, set.preimage_mul_left_singleton, eq_self_iff_true,
    inv_inv, set.singleton_eq_singleton_iff],
end

variables {G}

-- PRed in #6669
@[to_additive]
def subgroup.topological_closure (H : subgroup G) : subgroup G :=
{ carrier := _root_.closure H,
  one_mem' := _root_.subset_closure H.one_mem,
  mul_mem' := λ a b ha hb, H.to_submonoid.top_closure_mul_self_subset ⟨a, b, ha, hb, rfl⟩,
  inv_mem' := begin
    change closure (H : set G) ⊆ (λ x : G, x⁻¹) ⁻¹' (closure H),
    conv_rhs { rw show (H : set G) = (λ x : G, x⁻¹) '' H, by ext ; simp },
    exact closure_subset_preimage_closure_image (continuous_inv : continuous (λ x : G, _)),
  end }

end
