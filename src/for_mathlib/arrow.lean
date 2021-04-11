import tactic
import category_theory.limits.has_limits
import category_theory.arrow

namespace category_theory

namespace arrow

universes v u

variables {C : Type u} [category.{v} C]

abbreviation left_func : arrow C ⥤ C := comma.fst _ _

abbreviation right_func : arrow C ⥤ C := comma.snd _ _

def left_to_right : (left_func : arrow C ⥤ C) ⟶ right_func :=
{ app := λ f, f.hom }

def limit_cone {J : Type v} [small_category J] (F : J ⥤ arrow C)
  (CL : limits.limit_cone (F ⋙ left_func))
  (CR : limits.limit_cone (F ⋙ right_func)) :
  limits.limit_cone F :=
{ cone :=
  { X :=
    { left := CL.cone.X,
      right := CR.cone.X,
      hom := CR.is_limit.lift ⟨_,CL.cone.π ≫ whisker_left _ left_to_right⟩ },
    π :=
    { app := λ j,
      { left := CL.cone.π.app _,
        right := CR.cone.π.app _ },
      naturality' := begin
        intros i j f,
        ext1,
        { dsimp,
          rw [category.id_comp, ← CL.cone.w],
          refl },
        { dsimp,
          rw [category.id_comp, ← CR.cone.w],
          refl },
      end
      } },
  is_limit :=
  { lift := λ S,
    { left := CL.is_limit.lift (left_func.map_cone _),
      right := CR.is_limit.lift (right_func.map_cone _),
      w' := begin
        apply CR.is_limit.hom_ext,
        intros j,
        simp only [functor.id_map, functor.map_cone_π_app, limits.is_limit.fac,
          whisker_left_app, comma.snd_map, limits.is_limit.fac_assoc,
          comma.fst_map, nat_trans.comp_app, category.assoc],
        erw left_to_right.naturality,
        refl,
      end
      },
    --fac' := _,
    uniq' := begin
      intros S m w,
      ext1,
      { dsimp at *,
        apply CL.is_limit.uniq (left_func.map_cone S) m.left,
        intros j,
        exact congr_arg (λ a, left_func.map a) (w j) },
      { dsimp at *,
        apply CR.is_limit.uniq (right_func.map_cone S) m.right,
        intros j,
        exact congr_arg (λ a, right_func.map a) (w j) },
    end } }.

instance {f g : arrow C} (ff : f ⟶ g) [is_iso ff.left] [is_iso ff.right] :
  is_iso ff :=
begin
  constructor,
  refine ⟨_,_,_⟩,
  refine ⟨inv ff.left, inv ff.right, _⟩,
  tidy,
end

end arrow

end category_theory
