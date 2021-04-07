import topology.category.Profinite
import category_theory.limits.creates
import category_theory.monad.limits

open category_theory

universe u

noncomputable
instance Profinite.to_Top.reflective : reflective.{u u} Profinite_to_Top :=
begin
  -- The mathlib PR fixes the universes in the correct place.
  haveI : reflective.{u u} (CompHaus_to_Top : CompHaus.{u} ⥤ Top.{u}) :=
    CompHaus_to_Top.reflective.{u u},
  exact reflective.comp Profinite.to_CompHaus CompHaus_to_Top
end

noncomputable
instance Profinite.to_Top.creates_limits : creates_limits Profinite_to_Top :=
monadic_creates_limits _

instance Profinite.has_limits : limits.has_limits Profinite :=
has_limits_of_has_limits_creates_limits Profinite_to_Top
