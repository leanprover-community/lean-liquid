import category_theory.yoneda
import condensed.basic
import condensed.is_proetale_sheaf
import algebra.category.Group.adjunctions
--import algebra.category.Group.filtered_colimits

--import category_theory.sites.sheafification

import condensed.ab

universe u

open category_theory

def Profinite.to_Condensed (T : Profinite.{u}) : CondensedSet :=
{ val := yoneda.obj T ⋙ ulift_functor.{u+1},
  property := begin
    rw (functor.is_proetale_sheaf_of_types_tfae (yoneda.obj T ⋙ ulift_functor.{u+1})).out 0 5,
    refine ⟨_,_,_⟩,
    { dsimp [functor.empty_condition],
      split,
      { rintros _ _ _,
        ext ⟨⟩ },
      { intros x,
        refine ⟨⟨Profinite.empty.elim _⟩, _⟩,
        ext } },
    { intros X Y,
      split,
      { intros x y h,
        dsimp at x y h,
        ext (t|t),
        { apply_fun (λ e, e.fst.down t) at h, exact h },
        { apply_fun (λ e, e.snd.down t) at h, exact h } },
      { rintros ⟨a,b⟩,
        refine ⟨⟨_⟩,_⟩,
        dsimp,
        refine Profinite.sum.desc _ _ a.down b.down,
        ext, refl, refl } },
    { intros X B π hh,
      split,
      { intros x y h,
        dsimp [yoneda, functor.map_to_equalizer] at h,
        ext t,
        obtain ⟨t,rfl⟩ := hh t,
        apply_fun (λ e, e.val.down t) at h,
        exact h },
      { rintros ⟨⟨t⟩,ht⟩,
        refine ⟨⟨Profinite.descend π t hh _⟩, _⟩,
        dsimp at ht,
        apply_fun (λ e, e.down) at ht,
        exact ht,
        dsimp [yoneda, ulift_functor, functor.map_to_equalizer],
        ext : 2,
        dsimp,
        apply Profinite.π_descend } }
  end } .

namespace CondensedAb

noncomputable
def free_on (S : CondensedSet.{u}) : Condensed.{u} Ab.{u+1} :=
(presheaf_to_Sheaf proetale_topology _).obj $
  (SheafOfTypes_to_presheaf _).obj S ⋙ AddCommGroup.free

def forget : Condensed.{u} Ab.{u+1} ⥤ CondensedSet :=
  Condensed.forget_to_CondensedType

noncomputable
def lift {S : CondensedSet.{u}} {T : Condensed.{u} Ab.{u+1}}
  (η : S ⟶ forget.obj T) :
  free_on S ⟶ T :=
proetale_topology.sheafify_lift
{ app := λ X, free_abelian_group.lift $ η.app X,
  naturality' := begin
    intros X Y f,
    apply free_abelian_group.lift.ext,
    intros t,
    dsimp,
    simp only [free_abelian_group.lift.of, comp_apply,
      free_abelian_group.map_of, AddCommGroup.free_map_coe],
    change ((S.1.map f) ≫ η.app Y) _ = _,
    rw η.naturality,
    refl,
  end } T.2 .

-- We need the fact that sheafification for Ab-valued presheaves arises from
-- sheafification of Type-valued presheaves.
def incl (S : CondensedSet.{u}) : S ⟶ forget.obj (free_on S) := sorry

@[simp]
lemma incl_lift {S : CondensedSet.{u}} {T : Condensed.{u} Ab.{u+1}}
  (η : S ⟶ forget.obj T) : incl S ≫ forget.map (lift η) = η := sorry

lemma lift_unique {S : CondensedSet.{u}} {T : Condensed.{u} Ab.{u+1}}
  (η : S ⟶ forget.obj T) (g : free_on S ⟶ T) (h : incl S ≫ forget.map g = η) :
  g = lift η := sorry

lemma hom_ext {S : CondensedSet.{u}} {T : Condensed.{u} Ab.{u+1}}
  (f g : free_on S ⟶ T) (h : incl S ≫ forget.map f = incl S ≫ forget.map g) :
  f = g :=
by rw [lift_unique (incl S ≫ forget.map f) f rfl, lift_unique (incl S ≫ forget.map g) g rfl, h]

end CondensedAb
