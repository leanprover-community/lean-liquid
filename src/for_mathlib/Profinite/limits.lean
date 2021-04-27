import for_mathlib.Top.limits
import for_mathlib.Fintype.basic
import topology.category.Profinite
--import category_theory.limits.creates
--import category_theory.monad.limits

open category_theory

universe u

namespace Profinite

/-- A limit cone for a functor into `Profinite.` -/
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

/-- `limit_cone_cone` is indeed a limit cone. -/
def limit_cone_cone_is_limit {J : Type u} [small_category J] (F : J ⥤ Profinite.{u}) :
  limits.is_limit (limit_cone_cone F) :=
{ lift := λ S, (Top.limit_cone'_is_limit _).lift (Profinite_to_Top.map_cone S),
  uniq' := λ S m h, (Top.limit_cone'_is_limit _).uniq (Profinite_to_Top.map_cone S) _ h }

/-- A bundled limit cone, constructed from `limit_cone_cone` and `limit_cone_cone_is_limit`. -/
def limit_cone {J : Type u} [small_category J] (F : J ⥤ Profinite.{u}) :
  limits.limit_cone F :=
{ cone := limit_cone_cone _,
  is_limit := limit_cone_cone_is_limit _ }

end Profinite
