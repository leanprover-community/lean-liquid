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

namespace Top

def limit_cone' {J : Type u} [small_category J] (F : J ⥤ Top.{u}) :
  limits.cone F :=
{ X := { α := { u : Π j : J, F.obj j | ∀ {i j : J} (f : i ⟶ j), F.map f (u i) = u j } },
  π :=
  { app := λ j,
    { to_fun := λ x, x.val j,
      continuous_to_fun := begin
        change continuous ((λ u : Π j : J, F.obj j, u j) ∘ subtype.val),
        continuity,
      end } } }

end Top

namespace Profinite

lemma hom_closed {X Y : Profinite.{u}} (f : X ⟶ Y) :
  is_closed_map f :=
begin
  intros C hC,
  apply is_compact.is_closed,
  apply is_compact.image _ f.continuous,
  apply is_closed.compact hC,
end

noncomputable
def iso_of_bijective {X Y : Profinite.{u}} (f : X ⟶ Y)
  (h : function.bijective f) : X ≅ Y :=
let E  := equiv.of_bijective _ h,
    hE : continuous E.symm :=
begin
  rw continuous_iff_is_closed,
  intros C hC,
  convert ← hom_closed f C hC,
  erw equiv.image_eq_preimage E,
end in
{ hom := f,
  inv := ⟨E.symm, hE⟩,
  hom_inv_id' := begin
    ext1 x,
    change E.inv_fun (E.to_fun x) = x,
    rw E.left_inv,
  end,
  inv_hom_id' := begin
    ext1 x,
    change E.to_fun (E.inv_fun x) = x,
    rw E.right_inv,
  end }

lemma is_iso_of_bijective {X Y : Profinite.{u}}
  (f : X ⟶ Y) (h : function.bijective f) : is_iso f :=
let E := iso_of_bijective f h in
is_iso.mk $ ⟨E.inv, by erw E.hom_inv_id, by erw E.inv_hom_id⟩

end Profinite
