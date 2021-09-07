import topology.category.CompHaus

namespace CompHaus

open category_theory

noncomputable instance : limits.preserves_limits (forget CompHaus) :=
by apply limits.comp_preserves_limits CompHaus_to_Top (forget Top)

end CompHaus
