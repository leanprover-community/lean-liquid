import topology.category.Top

open category_theory

universe u

namespace Top

/-- An alternative limit cone to `Top.limit_cone`. 
  This is useful for expressing the limit as a subspace of a product. -/
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

/-- The alternative limit cone is indeed a limit cone. -/
def limit_cone'_is_limit {J : Type u} [small_category J] (F : J ⥤ Top.{u}) :
  limits.is_limit (limit_cone' F) :=
{ lift := λ S,
  { to_fun := λ x, ⟨λ j, S.π.app _ x, λ i j f, by {dsimp, erw ← S.w f, refl}⟩ },
  uniq' := begin
    intros S m h,
    ext : 3,
    dsimp,
    simpa [← h],
  end }.

end Top
