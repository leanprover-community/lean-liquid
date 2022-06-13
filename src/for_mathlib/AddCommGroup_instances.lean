import algebra.category.Group.abelian

open category_theory
open category_theory.limits

namespace AddCommGroup

universes u

instance : has_colimits_of_size.{u} Ab.{u+1} :=
has_colimits_of_size_shrink.{u u (u+1) (u+1)} Ab.{u+1}

instance : has_limits_of_size.{u} Ab.{u+1} :=
has_limits_of_size_shrink.{u u (u+1) (u+1)} Ab.{u+1}

end AddCommGroup
