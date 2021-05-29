import algebra.module
.

-- PR'd as #7746 (with its nat/rat cousins)

namespace add_monoid_hom

variables (M₁ M₂ : Type*) [add_comm_group M₁] [add_comm_group M₂]

lemma to_int_linear_map_injective :
  function.injective (@to_int_linear_map M₁ M₂ _ _) :=
by { intros f g h, ext, exact linear_map.congr_fun h x }

end add_monoid_hom
