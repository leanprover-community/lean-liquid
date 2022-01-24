import category_theory.yoneda
import condensed.basic
import condensed.is_proetale_sheaf
import condensed.extr.equivalence
import algebra.category.Group.adjunctions
import for_mathlib.SheafOfTypes_sheafification
import for_mathlib.yoneda
--import algebra.category.Group.filtered_colimits

import category_theory.limits.functor_category
import category_theory.sites.limits

--import condensed.ab

universe u

open category_theory

def Profinite.to_Condensed (T : Profinite.{u}) : CondensedSet :=
{ val := yoneda'.{u+1}.obj T, --⋙ ulift_functor.{u+1},
  cond := begin
    rw is_sheaf_iff_is_sheaf_of_type,
    rw (functor.is_proetale_sheaf_of_types_tfae (yoneda'.obj T)).out 0 5,
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

@[simps]
def Profinite_to_Condensed : Profinite ⥤ CondensedSet :=
{ obj := λ X, X.to_Condensed,
  map := λ X Y f, ⟨whisker_right (yoneda.map f) _⟩,
  map_id' := λ X, by { ext1, dsimp, erw [yoneda.map_id, whisker_right_id], refl },
  map_comp' := λ X Y Z f g, by { ext1, dsimp,
    erw [yoneda.map_comp, whisker_right_comp] } }

def Top.to_Condensed (T : Top.{u}) : CondensedSet :=
{ val := Profinite.to_Top.op ⋙ yoneda'.{u+1}.obj T,
  cond := begin
    rw is_sheaf_iff_is_sheaf_of_type,
    rw (functor.is_proetale_sheaf_of_types_tfae
      (Profinite.to_Top.op ⋙ yoneda'.obj T)).out 0 5,
    refine ⟨_,_,_⟩,
    { dsimp [functor.empty_condition],
      split,
      { rintros _ _ _,
        ext ⟨⟩ },
      { intros x,
        dsimp,
        refine ⟨⟨⟨λ x, x.elim, by continuity⟩⟩, _⟩,
        ext } },
    { intros X Y,
      split,
      { intros x y h,
        dsimp at x y h,
        ext (t|t),
        { apply_fun (λ e, e.fst.down t) at h, exact h },
        { apply_fun (λ e, e.snd.down t) at h, exact h } },
      { rintros ⟨a,b⟩,
        dsimp [ulift_functor] at a b,
        refine ⟨⟨⟨_,_⟩⟩,_⟩,
        { dsimp [Profinite.sum],
          intros t,
          exact sum.rec_on t a.down b.down },
        { dsimp,
          apply continuous_sup_dom,
          { apply continuous_coinduced_dom, exact a.down.continuous },
          { apply continuous_coinduced_dom, exact b.down.continuous } },
        { ext, refl, refl } } },
    { intros X B π hh,
      split,
      { intros x y h,
        dsimp [yoneda, functor.map_to_equalizer] at h,
        ext t,
        obtain ⟨t,rfl⟩ := hh t,
        apply_fun (λ e, e.val.down t) at h,
        exact h },
      { rintros ⟨⟨t⟩,ht⟩,
        refine ⟨⟨Profinite.descend_to_Top π t hh _⟩, _⟩,
        dsimp at ht,
        apply_fun (λ e, e.down) at ht,
        exact ht,
        dsimp [yoneda, ulift_functor, functor.map_to_equalizer],
        ext : 2,
        dsimp,
        apply Profinite.π_descend_to_Top,
      } }
  end }

@[simps]
def Top_to_Condensed : Top ⥤ CondensedSet :=
{ obj := λ X, X.to_Condensed,
  map := λ X Y f, ⟨whisker_left _ $ whisker_right (yoneda.map f) _⟩,
  map_id' := begin
    intros X,
    ext1,
    dsimp,
    erw [yoneda.map_id, whisker_right_id, whisker_left_id],
    refl,
  end,
  map_comp' := begin
    intros X Y Z f g,
    ext1,
    dsimp,
    erw [yoneda.map_comp, whisker_right_comp, whisker_left_comp],
  end }

open opposite

@[simps]
def Condensed.evaluation (C : Type*) [category C] (S : Profinite) :
  Condensed C ⥤ C :=
Sheaf_to_presheaf _ _ ⋙ (evaluation _ _).obj (op S)

noncomputable instance {C : Type*} [category C]
  [limits.has_limits C] (S : Profinite.{u}) :
  limits.preserves_limits (Condensed.evaluation C S) :=
begin
  apply_with limits.comp_preserves_limits { instances := ff },
  swap, apply_instance,
  have e : creates_limits (Sheaf_to_presheaf proetale_topology.{u} C) :=
     Sheaf.category_theory.Sheaf_to_presheaf.category_theory.creates_limits.{(u+2) u (u+1)},
  apply_with category_theory.preserves_limits_of_creates_limits_and_has_limits { instances := ff },
  exact e,
  apply_instance
end

@[simps]
def CondensedSet.evaluation (S : Profinite) : CondensedSet.{u} ⥤ Type (u+1) :=
Sheaf_to_presheaf _ _ ⋙ (evaluation _ _).obj (op S)

noncomputable instance (S : Profinite.{u}) :
  limits.preserves_limits (CondensedSet.evaluation S) :=
begin
  apply_with limits.comp_preserves_limits { instances := ff },
  swap, apply_instance,
  have e : creates_limits (Sheaf_to_presheaf proetale_topology.{u} (Type (u+1))) :=
     Sheaf.category_theory.Sheaf_to_presheaf.category_theory.creates_limits.{(u+2) u (u+1)},
  apply_with category_theory.preserves_limits_of_creates_limits_and_has_limits { instances := ff },
  exact e,
  apply_instance
end

universe w
open category_theory.limits

variables (C : Type w) [category.{u+1} C]
  [has_limits C] [has_zero_morphisms C] [has_finite_biproducts C]

instance preserves_colimits_Condensed_evaluation
  (S : Profinite.{u}) (C : Type w) [category.{u+1} C]
  [has_limits C] [has_zero_morphisms C] [has_finite_biproducts C] :
  limits.preserves_colimits (Condensed.evaluation C S) := sorry

-- TODO: Move this
instance : has_finite_biproducts Ab :=
has_finite_biproducts.of_has_finite_products

-- sanity check
example (S : Profinite.{u}) [projective S] :
  limits.preserves_colimits (Condensed.evaluation Ab.{u+1} S) :=
preserves_colimits_Condensed_evaluation S Ab
