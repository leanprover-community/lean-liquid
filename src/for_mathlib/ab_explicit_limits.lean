import algebra.category.Group.limits

universe u

namespace AddCommGroup

open category_theory
open category_theory.limits

variables {J : Type u} [category_theory.small_category J] (K : J ⥤ AddCommGroup.{u})

instance : add_comm_group (K ⋙ category_theory.forget _).sections :=
{ add := λ u v, ⟨ u + v, sorry⟩,
  add_assoc := sorry,
  zero := ⟨0, sorry⟩,
  zero_add := sorry,
  add_zero := sorry,
  nsmul := λ n t, ⟨ n • t, sorry⟩,
  nsmul_zero' := sorry,
  nsmul_succ' := sorry,
  neg := λ t, ⟨ -t, sorry ⟩,
  sub := λ u v, ⟨ u - v, sorry ⟩,
  sub_eq_add_neg := sorry,
  zsmul := λ n t, ⟨ n • t, sorry ⟩,
  zsmul_zero' := sorry,
  zsmul_succ' := sorry,
  zsmul_neg' := sorry,
  add_left_neg := sorry,
  add_comm := sorry }

def explicit_limit_cone : cone K :=
{ X := AddCommGroup.of (K ⋙ category_theory.forget _).sections,
  π :=
  { app := λ j,
    { to_fun := λ t, t.1 j,
      map_zero' := sorry,
      map_add' := sorry },
    naturality' := sorry } }

def explicit_limit_cone_is_limit : is_limit (explicit_limit_cone K) :=
{ lift := λ S,
  { to_fun := λ t, ⟨ λ j, S.π.app j t, sorry⟩,
    map_zero' := sorry,
    map_add' := sorry },
  fac' := sorry,
  uniq' := sorry }

end AddCommGroup
