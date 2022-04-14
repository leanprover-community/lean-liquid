import condensed.is_proetale_sheaf
import condensed.adjunctions
import category_theory.limits.filtered_colimit_commutes_finite_limit

open category_theory
open category_theory.limits

universe u
variables
  {J : Type (u+1)} [small_category J] [is_filtered J]
  {C : Type (u+2)}
  [category.{u+1} C]
  [concrete_category.{u+1} C]
  [has_limits C]
  [has_colimits_of_shape J C]
  [preserves_colimits_of_shape J (forget C)]
  [reflects_limits (forget C)]
  [preserves_limits (forget C)]
  (F : J ⥤ Condensed.{u} C)

open opposite

namespace is_sheaf_colimit_presheaf_aux

namespace empty

variables (G : J ⥤ Profinite.{u}ᵒᵖ ⥤ C)

noncomputable
def comparison_component (j : J) :
  (G.obj j).obj (op Profinite.empty) ⟶ ⊤_ _ := terminal.from _

variables [∀ j, is_iso (comparison_component G j)]

noncomputable
def first_iso : (colimit G).obj (op Profinite.empty) ≅
  colimit (limit (functor.empty _ ⋙ G.flip)) :=
let e₁ := is_colimit_of_preserves ((evaluation _ _).obj (op Profinite.empty))
  (colimit.is_colimit G),
    e₂ := e₁.cocone_point_unique_up_to_iso (colimit.is_colimit _),
    e₃ : G ⋙ (evaluation Profiniteᵒᵖ C).obj (op Profinite.empty) ≅
      limit (functor.empty Profiniteᵒᵖ ⋙ G.flip) :=
      nat_iso.of_components
      (λ j,
        let e₄ := is_limit_of_preserves ((evaluation _ _).obj j)
          (limit.is_limit (functor.empty _ ⋙ G.flip)),
            e₅ := (limit.is_limit _).cone_point_unique_up_to_iso e₄,
            e₆ : functor.empty C ≅
              (functor.empty Profiniteᵒᵖ ⋙ G.flip) ⋙ (evaluation J C).obj j :=
              nat_iso.of_components (λ i, i.elim) (λ i, i.elim) in
        as_iso (comparison_component G j) ≪≫
          has_limit.iso_of_nat_iso e₆ ≪≫ e₅)
      sorry in
e₂ ≪≫ has_colimit.iso_of_nat_iso e₃

noncomputable
def second_iso : colimit (limit (functor.empty _ ⋙ G.flip)) ≅
  limit (colimit (functor.empty _ ⋙ G.flip).flip) :=
  colimit_limit_iso _

noncomputable
def third_iso : limit (colimit (functor.empty _ ⋙ G.flip).flip) ≅ ⊤_ _ :=
has_limit.iso_of_nat_iso $ nat_iso.of_components (λ i, i.elim) (λ i, i.elim)

noncomputable
def comparison : (colimit G).obj (op Profinite.empty) ⟶ ⊤_ _ := terminal.from _

theorem is_iso_comparison : is_iso (comparison G) :=
begin
  suffices : comparison G = (first_iso G).hom ≫ (second_iso G).hom ≫ (third_iso G).hom,
  { rw this, apply_instance },
  simp,
end

end empty

end is_sheaf_colimit_presheaf_aux
open is_sheaf_colimit_presheaf_aux

/-
variables {K : Type (u+1)} [small_category K] [fin_category K]
  (E : K ⥤ Profinite.{u}ᵒᵖ) [has_limit E] (G : J ⥤ Profinite.{u}ᵒᵖ ⥤ C)
  [∀ j, preserves_limits_of_shape K (G.obj j)]

noncomputable
def comparison_map_component (j : J) : (G.obj j).obj (limit E) ⟶ limit (E ⋙ G.obj j) :=
limit.lift (E ⋙ G.obj j) $ (G.obj j).map_cone (limit.cone E)

noncomputable
def comparison_map : (colimit G).obj (limit E) ⟶ limit (E ⋙ colimit G) :=
limit.lift (E ⋙ colimit G) $ (colimit G).map_cone (limit.cone E)

noncomputable
def first_iso : (colimit G).obj (limit E) ≅ colimit (limit (E ⋙ G.flip)) :=
let e := is_colimit_of_preserves ((evaluation _ _).obj (limit E))
  (colimit.is_colimit G),
  ee := e.cocone_point_unique_up_to_iso (colimit.is_colimit _),
  tt : G ⋙ (evaluation Profiniteᵒᵖ C).obj (limit E) ≅ limit (E ⋙ G.flip) :=
    nat_iso.of_components (λ j, begin
      dsimp,
      refine (is_limit_of_preserves (G.obj j) (limit.is_limit E)).cone_point_unique_up_to_iso
        (limit.is_limit _) ≪≫ _,
      refine _ ≪≫ (limit.is_limit _).cone_point_unique_up_to_iso
        ((is_limit_of_preserves ((evaluation _ _).obj j) (limit.is_limit _))),
      dsimp,
      refine has_limit.iso_of_nat_iso _,
      refine nat_iso.of_components _ _,
      intros k, exact iso.refl _,
      intros k₁ k₂ f, dsimp, simp,
    end) sorry in
ee ≪≫ has_colimit.iso_of_nat_iso tt

noncomputable
def second_iso : colimit (limit (E ⋙ G.flip)) ≅ limit (colimit (E ⋙ G.flip).flip) :=
  colimit_limit_iso _

noncomputable
def third_iso : limit (colimit (E ⋙ G.flip).flip) ≅ limit (E ⋙ colimit G) :=
has_limit.iso_of_nat_iso $
nat_iso.of_components (λ k,
  let ee := (is_colimit_of_preserves ((evaluation _ _).obj k)
    (colimit.is_colimit (E ⋙ G.flip).flip)).cocone_point_unique_up_to_iso
    (colimit.is_colimit _) in
  ee ≪≫
  begin
    dsimp,
    refine _ ≪≫
      (colimit.is_colimit _).cocone_point_unique_up_to_iso
      ((is_colimit_of_preserves ((evaluation _ _).obj (E.obj k)) (colimit.is_colimit _))),
    dsimp,
    refine has_colimit.iso_of_nat_iso _,
    refine nat_iso.of_components _ _,
    intros j, exact iso.refl _,
    intros i j f, dsimp, simp,
  end) sorry

lemma is_iso : is_iso (comparison_map E G) :=
begin
  suffices : comparison_map E G =
    (first_iso E G).hom ≫ (second_iso E G).hom ≫ (third_iso E G).hom,
  { rw this, apply_instance },
  sorry,
end

-- Use the comparison map above
variable (K)
def key : preserves_limits_of_shape K (colimit G) := sorry

end is_sheaf_colimit_presheaf_aux
open is_sheaf_colimit_presheaf_aux

theorem empty_condition_iff_preserves (G : Profiniteᵒᵖ ⥤ C) :
  G.empty_condition' ↔
  nonempty (preserves_limits_of_shape (discrete pempty.{u+1}) G) := sorry

theorem product_condition_iff_preserves (G : Profiniteᵒᵖ ⥤ C) :
  G.product_condition' ↔
  nonempty (preserves_limits_of_shape (discrete walking_pair.{u+1}) G) := sorry

theorem equalizer_condition_iff_preserves (G : Profiniteᵒᵖ ⥤ C) :
  G.equalizer_condition' ↔
  nonempty (preserves_limits_of_shape (walking_parallel_pair.{u+1}) G) := sorry
-/

lemma is_sheaf_colimit_presheaf :
  presheaf.is_sheaf proetale_topology (colimit (F ⋙ Sheaf_to_presheaf _ _)) :=
begin
  --rw is_sheaf_iff_is_sheaf_of_type,
  let G := (colimit (F ⋙ Sheaf_to_presheaf _ _)),
  let Gs := F ⋙ Sheaf_to_presheaf _ _,
  have hGs : ∀ j, presheaf.is_sheaf proetale_topology (Gs.obj j),
  { intros j, exact (F.obj j).2 },
  have hGsempty : ∀ j, (Gs.obj j).empty_condition',
  { intros j, specialize hGs j,
    rw (Gs.obj j).is_proetale_sheaf_tfae.out 0 3 at hGs,
    exact hGs.1 },
  have hGsprod : ∀ j, (Gs.obj j).product_condition',
  { intros j, specialize hGs j,
    rw (Gs.obj j).is_proetale_sheaf_tfae.out 0 3 at hGs,
    exact hGs.2.1 },
  have hGseq : ∀ j, (Gs.obj j).equalizer_condition',
  { intros j, specialize hGs j,
    rw (Gs.obj j).is_proetale_sheaf_tfae.out 0 3 at hGs,
    exact hGs.2.2 },
  rw G.is_proetale_sheaf_tfae.out 0 3,
  refine ⟨_,_,_⟩,
  { apply_with empty.is_iso_comparison { instances := ff },
    exact hGsempty,
    all_goals { apply_instance } },
  { sorry },
  { sorry }
end
