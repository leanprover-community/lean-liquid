import category_theory.sites.sheafification

namespace category_theory

open category_theory.limits

universes w v u
variables {C : Type u} [category.{v} C] [has_pullbacks C] (J : grothendieck_topology C)
variables {D : Type w} [category.{max v u} D]
  [concrete_category.{max v u} D]
  [preserves_limits (forget D)]
  --[∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.cover X), has_multiequalizer (S.index P)]
  [has_limits D] -- ← this should be generalized.
  [∀ (X : C), has_colimits_of_shape (J.cover X)ᵒᵖ D]
  [∀ (X : C), preserves_colimits_of_shape (J.cover X)ᵒᵖ (forget D)]
  [reflects_isomorphisms (forget D)]

noncomputable theory

open grothendieck_topology

def multicospan_forget (P : Cᵒᵖ ⥤ D) (X) (W : J.cover X) :
  (W.index (P ⋙ forget D)).multicospan ≅ (W.index P).multicospan ⋙ forget D :=
nat_iso.of_components
( λ i,
match i with
| walking_multicospan.left a := eq_to_iso rfl
| walking_multicospan.right b := eq_to_iso rfl
end )
begin
  rintros (a|b) (a|b) (f|f|f),
  any_goals {
    dsimp [multicospan_forget._match_1, cover.index, limits.multicospan_index.multicospan],
    change _ = _ ≫ (forget D).map _,
    rw [(forget D).map_id, category.id_comp, category.id_comp],
    refl },
  all_goals {
    dsimp [multicospan_forget._match_1, cover.index, limits.multicospan_index.multicospan],
    simpa },
end

def diagram_forget (P : Cᵒᵖ ⥤ D) (X) :
  J.diagram (P ⋙ forget D) X ≅ J.diagram P X ⋙ forget D :=
nat_iso.of_components (λ W,
begin
  refine has_limit.iso_of_nat_iso (multicospan_forget J P X W.unop) ≪≫ _,
  refine (limit.is_limit _).cone_point_unique_up_to_iso
    (is_limit_of_preserves (forget D) (limit.is_limit _))
end ) begin
  sorry
end

def plus_forget (P : Cᵒᵖ ⥤ D) :
  J.plus_obj (P ⋙ forget D) ≅ J.plus_obj P ⋙ forget D :=
nat_iso.of_components (λ X,
begin
  refine has_colimit.iso_of_nat_iso (diagram_forget J P X.unop) ≪≫ _,
  refine (colimit.is_colimit _).cocone_point_unique_up_to_iso
    (is_colimit_of_preserves (forget D) (colimit.is_colimit _)),
end) begin
  sorry
end

lemma plus_map_plus_forget_hom {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) :
  J.plus_map (whisker_right η (forget D)) ≫ (plus_forget J Q).hom =
  (plus_forget J P).hom ≫ whisker_right (J.plus_map η) _ :=
begin
  sorry
end

lemma to_plus_plus_forget_hom (P : Cᵒᵖ ⥤ D) :
  J.to_plus (P ⋙ forget D) ≫ (plus_forget J P).hom = whisker_right (J.to_plus _) _ :=
begin
  sorry
end

def sheafify_forget (P : Cᵒᵖ ⥤ D) :
  J.sheafify (P ⋙ forget D) ≅ J.sheafify P ⋙ forget D :=
(J.plus_functor _).map_iso (plus_forget J P) ≪≫ plus_forget _ _

lemma to_sheafify_sheafify_forget_hom (P : Cᵒᵖ ⥤ D) :
  J.to_sheafify (P ⋙ forget D) ≫ (sheafify_forget J P).hom = whisker_right (J.to_sheafify P) _ :=
begin
  dsimp only [sheafify_forget, to_sheafify, functor.map_iso, iso.trans_hom],
  rw whisker_right_comp,
  rw [← to_plus_plus_forget_hom, category.assoc, category.assoc],
  congr' 1,
  dsimp only [plus_functor],
  change (J.plus_functor _).map _ ≫ (J.plus_functor _).map _ ≫ _ = _,
  rw [← category.assoc, ← functor.map_comp],
  rw to_plus_plus_forget_hom,
  dsimp only [plus_functor],
  rw plus_map_plus_forget_hom,
end

lemma sheafify_forget_hom (P : Cᵒᵖ ⥤ D) :
  (sheafify_forget J P).hom = J.sheafify_lift (whisker_right (J.to_sheafify _) _)
begin
  rw ← presheaf.is_sheaf_iff_is_sheaf_forget,
  exact plus.is_sheaf_plus_plus J P,
end :=
begin
  apply J.sheafify_lift_unique,
  rw to_sheafify_sheafify_forget_hom,
end

end category_theory
