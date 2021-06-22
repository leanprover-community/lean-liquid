import ring_theory.finiteness
import linear_algebra.free_module
import linear_algebra.dual

variables (R M : Type*) [semiring R] [add_comm_group M] [module R M]

lemma module.finite.of_basis {ι : Type*} [fintype ι] (b : basis ι R M) : module.finite R M :=
begin
  classical,
  refine ⟨⟨finset.univ.image b, _⟩⟩,
  simp only [set.image_univ, finset.coe_univ, finset.coe_image, basis.span_eq],
end

-- we might need to restrict to commutative rings?
instance [module.finite R M] [module.free R M] : fintype (module.free.choose_basis_index R M) :=
sorry

section
variables [module.finite ℤ M] [module.free ℤ M]

-- generalize?
instance : module.finite ℤ (M →+ ℤ) :=
begin
  classical,
  let b := module.free.choose_basis ℤ M,
  exact module.finite.of_basis ℤ _ (b.dual_basis.map add_monoid_hom_lequiv_int.symm),
end

-- generalize?
instance : module.free ℤ (M →+ ℤ) :=
begin
  classical,
  let b := module.free.choose_basis ℤ M,
  exact module.free.of_basis (b.dual_basis.map add_monoid_hom_lequiv_int.symm),
end

end
