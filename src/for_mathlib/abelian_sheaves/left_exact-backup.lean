/-
import category_theory.sites.limits

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

noncomputable
def mk_cone_aux {K : Type (max v u)} [small_category K] [fin_category K] [has_limits_of_shape K D]
  {F : K ⥤ Cᵒᵖ ⥤ D} (E : cone F) (X : Cᵒᵖ) :
  cone (F ⋙ J.plus_functor D ⋙ (evaluation _ _).obj X) :=
{ X := (J.plus_obj E.X).obj X,
  π :=
  { app := λ k, ((J.plus_functor D).map (E.π.app k)).app X,
    naturality' := begin
      intros i j f,
      dsimp only [functor.comp_map, evaluation],
      conv_lhs { congr, dsimp },
      erw category.id_comp,
      rw [← nat_trans.comp_app, ← (J.plus_functor D).map_comp, E.w f],
    end } }

open opposite

noncomputable
def diagram_map_nat_trans {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (X : C) :
  J.diagram P X ⟶ J.diagram Q X :=
{ app := λ W, multiequalizer.lift _ _ (λ I, multiequalizer.ι _ I ≫ η.app _) sorry,
  naturality' := sorry }

noncomputable
def uncurried_diagram {K : Type (max v u)} [small_category K] [fin_category K]
  [has_limits_of_shape K D] (F : K ⥤ Cᵒᵖ ⥤ D) (X : Cᵒᵖ) :
  K × (J.cover X.unop)ᵒᵖ ⥤ D :=
{ obj := λ t, (J.diagram (F.obj t.1) X.unop).obj t.2,
  map := λ t1 t2 f, (J.diagram _ _).map f.2 ≫ (J.diagram_map_nat_trans (F.map f.1) _).app _,
  map_id' := sorry,
  map_comp' := sorry }

noncomputable
def functor_diagram {K : Type (max v u)} [small_category K] [fin_category K]
  [has_limits_of_shape K D] (F : K ⥤ Cᵒᵖ ⥤ D) (X : Cᵒᵖ) :
  K ⥤ (J.cover X.unop)ᵒᵖ ⥤ D :=
{ obj := λ k, J.diagram (F.obj k) X.unop,
  map := λ i j f, J.diagram_map_nat_trans (F.map f) _,
  map_id' := sorry,
  map_comp' := sorry }

noncomputable
def uncurried_diagram_cone {K : Type (max v u)} [small_category K] [fin_category K]
  [has_limits_of_shape K D] {F : K ⥤ Cᵒᵖ ⥤ D} (E : cone F) (X : Cᵒᵖ) :
  cone (J.functor_diagram F X) :=
{ X := J.diagram E.X (unop X),
  π :=
  { app := λ k, J.diagram_map_nat_trans (E.π.app k) _,
    naturality' := sorry } }
--  J.diagram E.X (unop X) ≅ limit (curry.obj (J.uncurried_diagram F X)) :=

noncomputable
def uncurried_diagram_to_cone {K : Type (max v u)} [small_category K] [fin_category K]
  [has_limits_of_shape K D] {F : K ⥤ Cᵒᵖ ⥤ D} (X : Cᵒᵖ) (E : cone (J.functor_diagram F X))
  (I : (J.cover X.unop)ᵒᵖ) (t : I.unop.arrow): cone F :=
{ X :=
  { obj := λ X, (E.X.obj I),
    map := λ X Y f, 𝟙 _,
    map_id' := sorry,
    map_comp' := sorry },
  π :=
  { app := λ k,
    { app := λ Y, begin
        dsimp,
        have := (E.π.app k).app I,
        dsimp [functor_diagram] at this,
        dsimp [diagram] at this,
        have := this ≫ multiequalizer.ι (I.unop.index (F.obj k)) t,
        dsimp [cover.index] at this,
      end,
      naturality' := _ },
    naturality' := _ } }

noncomputable
def is_limit_uncurried_diagram_cone {K : Type (max v u)} [small_category K] [fin_category K]
  [has_limits_of_shape K D] {F : K ⥤ Cᵒᵖ ⥤ D} (E : cone F) (hE : is_limit E) (X : Cᵒᵖ) :
  is_limit (J.uncurried_diagram_cone E X) :=
{ lift := λ S, begin
    dsimp [uncurried_diagram_cone],
    have := hE.lift,
    let T : cone F := ⟨_,_⟩,
    rotate,
  end,
  fac' := _,
  uniq' := _ }

noncomputable
def is_limit_mk_cone_aux {K : Type (max v u)} [small_category K] [fin_category K]
  [has_limits_of_shape K D] {F : K ⥤ Cᵒᵖ ⥤ D} (E : cone F) (hE : is_limit E) (X : Cᵒᵖ) :
  is_limit (mk_cone_aux J E X) :=
{ lift := λ S, begin
    dsimp [mk_cone_aux],
    let e := curry.obj (category_theory.prod.swap (J.cover X.unop)ᵒᵖ K ⋙ J.uncurried_diagram F X),
    let ee := colimit e,
    change _ ⟶ ee ⋙ lim,
  end,
  fac' := _,
  uniq' := _ }

def is_limit_evaluation_map_plus_functor
  {K : Type (max v u)} [small_category K] [fin_category K] [has_limits_of_shape K D]
  {F : K ⥤ Cᵒᵖ ⥤ D} (E : cone F) (hE : is_limit E) (X : Cᵒᵖ) :
  is_limit (((evaluation Cᵒᵖ D).obj X).map_cone ((J.plus_functor D).map_cone E)) :=
begin
  change is_limit ((J.plus_functor D ⋙ (evaluation Cᵒᵖ D).obj X).map_cone E),
  apply is_limit_mk_cone_aux _ _ hE,
  apply_instance
end

noncomputable def is_limit_plus_of_is_limit {K : Type (max v u)}
  [small_category K] [fin_category K] [has_limits_of_shape K D]
  {F : K ⥤ Cᵒᵖ ⥤ D} (E : cone F) (hE : is_limit E) :
  is_limit ((J.plus_functor D).map_cone E) :=
begin
  apply evaluation_jointly_reflects_limits,
  intros X,
  apply is_limit_evaluation_map_plus_functor _ _ hE,
  swap, apply_instance,
  --intros Y,
  --apply is_limit_of_preserves _ hE,
  --apply_instance,
end

noncomputable
instance {K : Type (max v u)} [small_category K] [fin_category K] [has_limits_of_shape K D] :
  preserves_limits_of_shape K (J.plus_functor D) :=
begin
  constructor,
  dsimp,
  intros F,
  constructor,
  intros E hE,
  apply is_limit_plus_of_is_limit _ _ hE,
  apply_instance,
end

noncomputable
instance preserves_limit_of_shape_presheaf_to_Sheaf {K : Type (max v u)} [small_category K]
  [fin_category K] [has_limits_of_shape K D] :
  preserves_limits_of_shape K (presheaf_to_Sheaf J D) :=
begin
  -- This can probably be simplified...
  constructor,
  dsimp,
  intros F,
  constructor,
  intros E hE,
  suffices h : is_limit ((Sheaf_to_presheaf J D).map_cone ((presheaf_to_Sheaf J D).map_cone E)),
  { let e := lifted_limit_is_limit h,
    have ee : lift_limit h ≅ (presheaf_to_Sheaf J D).map_cone E,
    { let d := lifted_limit_maps_to_original h,
      let dd := (cones.forget _).map_iso d,
      fapply cones.ext,
      { refine ⟨dd.hom, dd.inv, dd.hom_inv_id, dd.inv_hom_id⟩ },
      intros j,
      have := d.hom.w j,
      exact this.symm },
    apply is_limit.of_iso_limit e ee },
  have h : (Sheaf_to_presheaf J D).map_cone ((presheaf_to_Sheaf J D).map_cone E)
    ≅ (sheafification J D).map_cone E := eq_to_iso rfl,
  suffices : is_limit ((sheafification J D).map_cone E),
  { apply is_limit.of_iso_limit this h },
  clear h,
  have h : (sheafification J D).map_cone E ≅
    (J.plus_functor D).map_cone ((J.plus_functor D).map_cone E) := eq_to_iso rfl,
  suffices : is_limit ((J.plus_functor D).map_cone ((J.plus_functor D).map_cone E)),
  { apply is_limit.of_iso_limit this h },
  apply is_limit_of_preserves,
  apply is_limit_of_preserves,
  exact hE,
end

end category_theory.grothendieck_topology
-/
