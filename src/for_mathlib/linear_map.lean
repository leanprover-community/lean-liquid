import linear_algebra.basic

variables {R M₁ M₂ M₃ : Type*} [comm_semiring R]
variables [add_comm_monoid M₁] [module R M₁]
variables [add_comm_monoid M₂] [module R M₂]
variables [add_comm_monoid M₃] [module R M₃]

namespace linear_map

@[simps]
def comp_hom : (M₂ →ₗ[R] M₃) →ₗ[R] (M₁ →ₗ[R] M₂) →ₗ[R] (M₁ →ₗ[R] M₃) :=
{ to_fun := λ g,
  { to_fun := λ f, g.comp f,
    map_add' := λ f₁ f₂, comp_add _ _ _,
    map_smul' := λ r f, comp_smul _ _ _ },
  map_add' := λ g₁ g₂, by { ext1 f, apply add_comp },
  map_smul' := λ r g, by { ext1 f, apply smul_comp } }

end linear_map
