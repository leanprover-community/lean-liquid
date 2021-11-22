import category_theory.sites.limits

import for_mathlib.concrete_filtered_colimit_commutes

namespace category_theory.grothendieck_topology

open category_theory
open category_theory.limits

universes w v u

variables {C : Type (max v u)} [category.{v} C] (J : grothendieck_topology C)
variables {D : Type w} [category.{max v u} D]
-- We need to sheafify
variables [concrete_category.{max v u} D]
variables [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.cover X), has_multiequalizer (S.index P)]
variables [preserves_limits (forget D)]
variables [∀ (X : C), has_colimits_of_shape (J.cover X)ᵒᵖ D]
variables [∀ (X : C), preserves_colimits_of_shape (J.cover X)ᵒᵖ (forget D)]
variables [reflects_isomorphisms (forget D)]

noncomputable theory

@[simps]
def map_diagram {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (X : C) :
  J.diagram P X ⟶ J.diagram Q X :=
{ app := λ W, multiequalizer.lift _ _ (λ i, multiequalizer.ι _ i ≫ η.app _) begin
    intros i,
    dsimp,
    simp,
    erw [← η.naturality, ← η.naturality, ← category.assoc,
      ← category.assoc, multiequalizer.condition],
    refl,
  end,
  naturality' := begin
    intros A B f,
    dsimp [diagram],
    ext,
    simpa,
  end }

@[simps]
def lim_diagram {K : Type (max v u)}
  [small_category K] [fin_category K] (F : K ⥤ Cᵒᵖ ⥤ D) (X : Cᵒᵖ) :
  K ⥤ (J.cover X.unop)ᵒᵖ ⥤ D :=
{ obj := λ i, J.diagram (F.obj i) _,
  map := λ i j e, J.map_diagram (F.map e) _,
  map_id' := begin
    intros k,
    ext,
    dsimp,
    simp,
    erw category.comp_id,
  end,
  map_comp' := begin
    intros i j k f g,
    ext,
    dsimp,
    simp,
  end }

def lim_diagram_cone_eval {K : Type (max v u)}
  [small_category K] [fin_category K]
  --[has_limits_of_shape K D]
  {F : K ⥤ Cᵒᵖ ⥤ D}
  (E : cone F) (X : Cᵒᵖ) (W : (J.cover X.unop)ᵒᵖ) :
  cone ((J.lim_diagram F X).flip.obj W) :=
{ X := (J.diagram E.X X.unop).obj W,
  π :=
  { app := λ k, (J.map_diagram (E.π.app k) _).app W,
    naturality' := sorry } }

open opposite

def is_limit_lim_diagram_cone_eval {K : Type (max v u)}
  [small_category K] [fin_category K]
  [has_limits_of_shape K D]
  {F : K ⥤ Cᵒᵖ ⥤ D}
  (E : cone F) (hE : is_limit E) (X : Cᵒᵖ) (W : (J.cover X.unop)ᵒᵖ) :
  is_limit (J.lim_diagram_cone_eval E X W) :=
{ lift := λ S, multiequalizer.lift _ _ (λ i,
    (is_limit_of_preserves ((evaluation _ D).obj (op i.Y)) hE).lift ⟨S.X,
    { app := λ k, S.π.app k ≫ multiequalizer.ι _ i,
      naturality' := sorry }⟩) sorry,
  fac' := sorry,
  uniq' := sorry }

def lim_diagram_cone {K : Type (max v u)}
  [small_category K] [fin_category K]
  --[has_limits_of_shape K D]
  {F : K ⥤ Cᵒᵖ ⥤ D}
  (E : cone F) (X : Cᵒᵖ) : cone (J.lim_diagram F X) :=
{ X := J.diagram E.X X.unop,
  π :=
  { app := λ k, J.map_diagram (E.π.app _) _,
    naturality' := sorry } }

def is_limit_lim_diagram_cone {K : Type (max v u)}
  [small_category K] [fin_category K]
  [has_limits_of_shape K D]
  {F : K ⥤ Cᵒᵖ ⥤ D}
  (E : cone F) (hE : is_limit E) (X : Cᵒᵖ) :
  is_limit (J.lim_diagram_cone E X) :=
{ lift := λ S,
  { app := λ W, (J.is_limit_lim_diagram_cone_eval E hE X W).lift ⟨S.X.obj W,
    { app := λ k, (S.π.app k).app W,
      naturality' := sorry }⟩,
    naturality' := sorry },
  fac' := sorry,
  uniq' := sorry }

def colimit_lim_diagram_iso {K : Type (max v u)}
  [small_category K] [fin_category K] (F : K ⥤ Cᵒᵖ ⥤ D) (X : Cᵒᵖ) :
  colimit (J.lim_diagram F X).flip ≅ F ⋙ J.plus_functor D ⋙ (evaluation Cᵒᵖ D).obj X :=
nat_iso.of_components (λ k,
  let h := is_colimit_of_preserves ((evaluation _ D).obj k)
    (colimit.is_colimit ((J.lim_diagram F X).flip)) in
  h.cocone_point_unique_up_to_iso (colimit.is_colimit _))
begin
  intros a b f,
  ext1,
  dsimp [is_colimit.cocone_point_unique_up_to_iso, colim_map, is_colimit.map],
  rw ← (colimit.ι (J.lim_diagram F X).flip j).naturality_assoc,
  erw [colimit_obj_iso_colimit_comp_evaluation_ι_app_hom,
    colimit_obj_iso_colimit_comp_evaluation_ι_app_hom_assoc,
    colimit.ι_desc],
  refl,
end

def is_limit_evaluation_plus_of_is_limit (K : Type (max v u))
  [small_category K] [fin_category K] [has_limits_of_shape K D] {F : K ⥤ Cᵒᵖ ⥤ D}
  (E : cone F) (hE : is_limit E)
  (X : Cᵒᵖ) : is_limit ((J.plus_functor D ⋙ (evaluation _ _).obj X).map_cone E) :=
{ lift := λ S, begin
    let e := colimit_limit_iso (J.lim_diagram F X)
      (J.lim_diagram_cone E X) (J.is_limit_lim_diagram_cone E hE X),
    refine _ ≫ e.inv,
    refine _ ≫ (has_limit.iso_of_nat_iso (J.colimit_lim_diagram_iso F X)).inv,
    refine limit.lift _ S,
  end,
  fac' := begin
    intros S j,
    dsimp only,
    rw ← (limit.is_limit (F ⋙ J.plus_functor D ⋙ (evaluation Cᵒᵖ D).obj X)).fac S j,
    simp only [category.assoc],
    congr' 1,
    simp only [iso.inv_comp_eq],
    dsimp,
    ext W : 2,
    dsimp [has_limit.iso_of_nat_iso, is_limit.map],
    simp,
    have := ι_colimit_limit_to_limit_colimit_of_is_limit_π (J.lim_diagram F X)
      (J.lim_diagram_cone E X) (J.is_limit_lim_diagram_cone E hE X) W j,
    slice_rhs 1 3 { erw this },
    dsimp,
    simp,
    congr' 1,
    erw colimit_obj_iso_colimit_comp_evaluation_ι_app_hom,
    refl,
  end,
  uniq' := begin
    intros S m hm,
    dsimp only,
    rw [iso.eq_comp_inv, iso.eq_comp_inv],
    ext,
    dsimp,
    simp,
    rw ← hm,
    congr' 1,
    ext W,
    simp,
    erw ι_colimit_limit_to_limit_colimit_of_is_limit_π_assoc (J.lim_diagram F X)
      (J.lim_diagram_cone E X) (J.is_limit_lim_diagram_cone E hE X) W j,
    congr' 1,
    erw colimit_obj_iso_colimit_comp_evaluation_ι_app_hom,
    refl,
  end }

instance plus_functor_preserves_finite_limits (K : Type (max v u))
  [small_category K] [fin_category K] [has_limits_of_shape K D] :
  preserves_limits_of_shape K (J.plus_functor D) :=
begin
  constructor, intros F, constructor, intros E hE,
  apply evaluation_jointly_reflects_limits,
  intros X,
  apply is_limit_evaluation_plus_of_is_limit _ _ _ hE,
  apply_instance
end

instance sheafification_preserves_finite_limits (K : Type (max v u))
  [small_category K] [fin_category K] [has_limits_of_shape K D] :
  preserves_limits_of_shape K (sheafification J D) :=
by { delta sheafification, apply_instance }

instance presheaf_to_Sheaf_preserves_finite_limits (K : Type (max v u))
  [small_category K] [fin_category K] [has_limits_of_shape K D] :
  preserves_limits_of_shape K (presheaf_to_Sheaf J D) :=
begin
  constructor, intros F, constructor, intros E hE,
  suffices h : is_limit ((Sheaf_to_presheaf J D).map_cone ((presheaf_to_Sheaf J D).map_cone E)),
  { let e := lifted_limit_is_limit h,
    let ee : lift_limit h ≅ (presheaf_to_Sheaf J D).map_cone E,
    { let d := lifted_limit_maps_to_original h,
      let dd := (cones.forget _).map_iso d,
      fapply cones.ext,
      { exact ⟨dd.hom, dd.inv, dd.hom_inv_id, dd.inv_hom_id⟩ },
      { intros j, exact (d.hom.w j).symm } },
    apply is_limit.of_iso_limit e ee },
  apply is_limit_of_preserves (sheafification J D) hE,
end

end category_theory.grothendieck_topology
