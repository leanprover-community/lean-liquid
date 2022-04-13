import condensed.is_proetale_sheaf
import condensed.adjunctions

open category_theory
open category_theory.limits

universe u
variables {J : Type (u+1)} [small_category J] [is_filtered J]
  (F : J ⥤ CondensedSet.{u})

lemma is_sheaf_colimit_presheaf :
  presheaf.is_sheaf proetale_topology (colimit (F ⋙ CondensedSet_to_presheaf)) :=
begin
  --rw is_sheaf_iff_is_sheaf_of_type,
  let G := (colimit (F ⋙ CondensedSet_to_presheaf)),
  rw G.is_proetale_sheaf_tfae.out 0 3,
  sorry
end
