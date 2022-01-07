import category_theory.yoneda
import condensed.basic
import condensed.is_proetale_sheaf
import algebra.category.Group.adjunctions
import for_mathlib.SheafOfTypes_sheafification
--import algebra.category.Group.filtered_colimits

--import category_theory.sites.sheafification

--import condensed.ab

universe u

open category_theory

def Profinite.to_Condensed (T : Profinite.{u}) : CondensedSet :=
{ val := yoneda.obj T ⋙ ulift_functor.{u+1},
  cond := begin
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

@[simps]
def Profinite_to_Condensed : Profinite ⥤ CondensedSet :=
{ obj := λ X, X.to_Condensed,
  map := λ X Y f, ⟨whisker_right (yoneda.map f) _⟩,
  map_id' := λ X, by { ext1, dsimp, erw [yoneda.map_id, whisker_right_id], refl },
  map_comp' := λ X Y Z f g, by { ext1, dsimp,
    erw [yoneda.map_comp, whisker_right_comp] } }

def Top.to_Condensed (T : Top.{u}) : CondensedSet :=
{ val := Profinite.to_Top.op ⋙ yoneda.obj T ⋙ ulift_functor.{u+1},
  cond := begin
    rw (functor.is_proetale_sheaf_of_types_tfae
      (Profinite.to_Top.op ⋙ yoneda.obj T ⋙ ulift_functor.{u+1})).out 0 5,
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
