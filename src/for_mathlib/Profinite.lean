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
      end } } }.

def limit_cone'_is_limit {J : Type u} [small_category J] (F : J ⥤ Top.{u}) :
  limits.is_limit (limit_cone' F) :=
{ lift := λ S,
  { to_fun := λ x, ⟨λ j, S.π.app _ x, λ i j f, by {dsimp, erw ← S.w f, refl}⟩ },
  uniq' := begin
    intros S m h,
    ext1 x,
    ext1,
    ext1 j,
    dsimp,
    erw ← h,
    refl,
  end }.

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

def limit_cone_cone {J : Type u} [small_category J] (F : J ⥤ Profinite.{u}) :
  limits.cone F :=
{ X :=
  { to_Top := (Top.limit_cone' (F ⋙ Profinite_to_Top)).X,
    is_compact := begin
      dsimp [Top.limit_cone'],
      erw ← compact_iff_compact_space,
      apply is_closed.compact,
      have : {u : Π (j : J), (F.obj j) | ∀ {i j : J} (f : i ⟶ j), (F.map f) (u i) = u j} =
        ⋂ (i j : J) (f : i ⟶ j), { u | F.map f (u i) = u j }, by tidy,
      rw this,
      apply is_closed_Inter, intros i, apply is_closed_Inter, intros j,
      apply is_closed_Inter, intros f,
      apply is_closed_eq,
      continuity,
    end,
    is_t2 := by {dsimp [Top.limit_cone'], apply_instance},
    is_totally_disconnected := by {dsimp [Top.limit_cone'], apply_instance} },
  π := { app := λ j, (Top.limit_cone' $ F ⋙ Profinite_to_Top).π.app j } }.

def limit_cone_cone_is_limit {J : Type u} [small_category J] (F : J ⥤ Profinite.{u}) :
  limits.is_limit (limit_cone_cone F) :=
{ lift := λ S, (Top.limit_cone'_is_limit _).lift (Profinite_to_Top.map_cone S),
  uniq' := λ S m h, (Top.limit_cone'_is_limit _).uniq (Profinite_to_Top.map_cone S) _ h }

def limit_cone {J : Type u} [small_category J] (F : J ⥤ Profinite.{u}) :
  limits.limit_cone F :=
{ cone := limit_cone_cone _,
  is_limit := limit_cone_cone_is_limit _ }

end Profinite
