import category_theory.limits.fubini

import for_mathlib.Profinite.extend
import for_mathlib.AddCommGroup.exact
import for_mathlib.limit_flip_comp_iso

import condensed.ab
import pseudo_normed_group.bounded_limits
import condensed.extr.lift_comphaus
import condensed.projective_resolution
import condensed.kernel_comparison

.

universes u v

noncomputable theory

open_locale nnreal

open category_theory category_theory.limits opposite pseudo_normed_group

-- move me
namespace CompHaus

variables {J : Type u} [small_category J]
  (F G : J ⥤ CompHaus.{u}) (α : F ⟶ G)
variables (cF : cone F) (cG : cone G) (hcF : is_limit cF) (hcG : is_limit cG)

def pt {X : CompHaus.{u}} (x : X) : (⊤_ CompHaus) ⟶ X :=
⟨λ _, x, continuous_const⟩

@[simps] def diagram_of_pt (y : cG.X) : J ⥤ CompHaus.{u} :=
{ obj := λ j, pullback (α.app j) (pt y ≫ cG.π.app j),
  map := λ i j f, pullback.lift (pullback.fst ≫ F.map f) pullback.snd
    (by rw [category.assoc, α.naturality, pullback.condition_assoc, category.assoc, cG.w]),
  map_id' := λ j, by apply pullback.hom_ext; dsimp; simp,
  map_comp' := λ i j k f g, by { apply pullback.hom_ext; dsimp; simp } }

.

@[simps] def cone_of_pt (y : cG.X) : cone (diagram_of_pt F G α cG y) :=
{ X := pullback (hcG.map cF α) (pt y),
  π :=
  { app := λ j, pullback.lift
      (pullback.fst ≫ cF.π.app _)
      pullback.snd
      (by rw [category.assoc, ← pullback.condition_assoc, is_limit.map_π]),
    naturality' := λ i j f, by apply pullback.hom_ext; dsimp; simp } }

.

def is_limit_cone_of_pt (y : cG.X) : is_limit (cone_of_pt F G α cF cG hcG y) :=
{ lift := λ S, pullback.lift
    (hcF.lift ⟨S.X,
    { app := λ j, S.π.app j ≫ pullback.fst,
      naturality' := begin
        intros i j f,
        dsimp,
        rw ← S.w f, dsimp [diagram_of_pt],
        simp only [category.id_comp, category.assoc, pullback.lift_fst],
      end }⟩)
    (terminal.from _)
    begin
      apply hcG.hom_ext, intros j, dsimp,
      simp only [category.assoc, is_limit.map_π, is_limit.fac_assoc, pullback.condition],
      ext, refl,
    end,
  fac' := begin
    intros s j, dsimp, apply pullback.hom_ext,
    { simp only [category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, is_limit.fac] },
    { simp only [eq_iff_true_of_subsingleton] },
  end,
  uniq' := begin
    intros s m hm,
    dsimp at m hm,
    apply pullback.hom_ext,
    { rw pullback.lift_fst,
      apply hcF.hom_ext, intros j,
      simp only [category.assoc, is_limit.fac, ← hm j, pullback.lift_fst] },
    { simp only [eq_iff_true_of_subsingleton] }
  end }

lemma is_limit.surjective_of_surjective [is_cofiltered J]
  (hα : ∀ j, function.surjective (α.app j)) :
  function.surjective (hcG.map cF α) := λ y,
let E := cone_of_pt F G α cF cG hcG y,
  hE : is_limit E := is_limit_cone_of_pt F G α cF cG hcF hcG y in
begin
  suffices : ∃ (e : (⊤_ CompHaus.{u}) ⟶ E.X),
    e ≫ (pullback.fst : E.X ⟶ cF.X) ≫ hcG.map cF α = pt y,
  { obtain ⟨e,he⟩ := this,
    use (terminal.from (CompHaus.of punit) ≫ e ≫ pullback.fst) punit.star,
    rw ← comp_apply,
    have : y = (terminal.from (CompHaus.of punit) ≫ pt y) punit.star := rfl,
    conv_rhs { rw this }, clear this, congr' 1,
    apply hcG.hom_ext,
    intros j,
    simp only [←he, category.assoc] },
  let E' := CompHaus_to_Top.map_cone E,
  let hE' : is_limit E' := is_limit_of_preserves CompHaus_to_Top hE,
  let ee : E' ≅ Top.limit_cone.{u u} _ :=
    hE'.unique_up_to_iso (Top.limit_cone_is_limit _),
  let e : E'.X ≅ (Top.limit_cone.{u u} _).X :=
    hE'.cone_point_unique_up_to_iso (Top.limit_cone_is_limit _),
  haveI : ∀ j : J, t2_space (((diagram_of_pt F G α cG y ⋙ CompHaus_to_Top).obj j)),
  { intros j, change t2_space ((diagram_of_pt F G α cG y).obj j), apply_instance },
  haveI : ∀ j : J, compact_space (((diagram_of_pt F G α cG y ⋙ CompHaus_to_Top).obj j)),
  { intros j, change compact_space ((diagram_of_pt F G α cG y).obj j), apply_instance },
  haveI : ∀ j : J, nonempty (((diagram_of_pt F G α cG y ⋙ CompHaus_to_Top).obj j)),
  { intro j, change nonempty ((diagram_of_pt F G α cG y).obj j),
    dsimp only [diagram_of_pt_obj],
    let y' := (terminal.from (CompHaus.of punit) ≫ pt y ≫ cG.π.app j) punit.star,
    obtain ⟨x', hx'⟩ := hα j y',
    refine ⟨(terminal.from (CompHaus.of punit) ≫ pullback.lift (pt x') (𝟙 _) _) punit.star⟩,
    ext z, exact hx', },
  have := Top.nonempty_limit_cone_of_compact_t2_cofiltered_system
    (diagram_of_pt F G α cG y ⋙ CompHaus_to_Top),
  obtain ⟨a⟩ := this,
  let b := e.inv a,
  use pt b,
  rw pullback.condition,
  refl,
end

-- Scott: perhaps life is easier if we use this version? I'm not too sure.
lemma is_limit.surjective_of_surjective' [is_cofiltered J]
  (hα : ∀ j, function.surjective (α.app j)) :
   function.surjective (lim_map α) :=
is_limit.surjective_of_surjective _ _ _ _ _ (limit.is_limit _) _ hα

end CompHaus

namespace CompHausFiltPseuNormGrp₁

-- move this
instance : has_zero_morphisms (CompHausFiltPseuNormGrp₁.{u}) :=
{ has_zero := λ M₁ M₂, ⟨0⟩,
  comp_zero' := λ _ _ f _, rfl,
  zero_comp' := λ _ _ _ f, by { ext, exact f.map_zero } }

variables {A B C : CompHausFiltPseuNormGrp₁.{u}}

structure strongly_exact (f : A ⟶ B) (g : B ⟶ C) (r : ℝ≥0 → ℝ≥0) : Prop :=
(comp_eq_zero : f ≫ g = 0)
(cond : ∀ c : ℝ≥0, g ⁻¹' {0} ∩ (filtration B c) ⊆ f '' (filtration A (r c)))
(large : id ≤ r)

lemma strongly_exact.exact {f : A ⟶ B} {g : B ⟶ C} {r : ℝ≥0 → ℝ≥0}
  (h : strongly_exact f g r) :
  exact ((to_PNG₁ ⋙ PseuNormGrp₁.to_Ab).map f) ((to_PNG₁ ⋙ PseuNormGrp₁.to_Ab).map g) :=
begin
  rw AddCommGroup.exact_iff',
  split,
  { ext x, have := h.comp_eq_zero, apply_fun (λ φ, φ.to_fun) at this, exact congr_fun this x },
  { intros y hy,
    obtain ⟨c, hc⟩ := B.exhaustive y,
    obtain ⟨a, ha, rfl⟩ := h.cond c ⟨_, hc⟩,
    { exact ⟨a, rfl⟩ },
    { simp only [set.mem_preimage, set.mem_singleton_iff], exact hy } },
end

-- TODO remove this; it's a redundant alias
@[simps obj_obj obj_map_apply map_app {fully_applied := ff}]
def Filtration : ℝ≥0 ⥤ CompHausFiltPseuNormGrp₁.{u} ⥤ CompHaus.{u} :=
CompHausFiltPseuNormGrp₁.level

instance mono_Filtration_map_app (c₁ c₂ : ℝ≥0) (h : c₁ ⟶ c₂) (M) :
  mono ((Filtration.map h).app M) :=
by { rw CompHaus.mono_iff_injective, convert injective_cast_le _ _ }

namespace strongly_exact
noncomputable theory

variables (f : A ⟶ B) (g : B ⟶ C) (r : ℝ≥0 → ℝ≥0) (c : ℝ≥0) (hrc : c ≤ r c)

variables {r c}

def c_le_rc : c ⟶ r c := hom_of_le $ hrc

/-- Given `f : A ⟶ B`, `P1` is the pullback `B_c ×_{B_{rc}} A_{rc}`. -/
def P1 : CompHaus :=
pullback ((Filtration.map (c_le_rc hrc)).app B) ((Filtration.obj (r c)).map f)

@[simps]
def pt {X : CompHaus} (x : X) : (⊤_ CompHaus) ⟶ X :=
⟨λ _, x, continuous_const⟩

/-- Given `g : B ⟶ C`, `P2` is the pullback `B_c ×_{C_c} {pt}`. -/
def P2 (c : ℝ≥0) : CompHaus :=
pullback ((Filtration.obj c).map g) (pt (0 : pseudo_normed_group.filtration C c))

def P1_to_P2 (hfg : f ≫ g = 0) : P1 f hrc ⟶ P2 g c :=
pullback.lift pullback.fst (terminal.from _)
begin
  rw [← cancel_mono ((Filtration.map (c_le_rc hrc)).app C), category.assoc,
    nat_trans.naturality, pullback.condition_assoc, ← functor.map_comp, hfg],
  refl,
end

lemma P1_to_P2_comp_fst (hfg : f ≫ g = 0) :
  P1_to_P2 f g hrc hfg ≫ pullback.fst = pullback.fst :=
pullback.lift_fst _ _ _

lemma surjective (h : strongly_exact f g r) :
  ∃ (hfg : f ≫ g = 0), ∀ c, function.surjective (P1_to_P2 f g (h.large c) hfg) :=
begin
  have hfg : f ≫ g = 0,
  { ext x, exact fun_like.congr_fun h.exact.w x },
  refine ⟨hfg, _⟩,
  intros c y,
  let π₁ : P2 g c ⟶ (Filtration.obj c).obj B := pullback.fst,
  have hy : (π₁ y).val ∈ g ⁻¹' {0} ∩ filtration B c,
  asyncI
  { refine ⟨_, (π₁ y).2⟩,
    simp only [subtype.val_eq_coe, set.mem_preimage, set.mem_singleton_iff],
    have w := @pullback.condition _ _ _ _ _
      ((Filtration.obj c).map g) (pt (0 : pseudo_normed_group.filtration C c)) _,
    have := (fun_like.congr_fun w y),
    exact congr_arg subtype.val this, },
  obtain ⟨x, hx, hfx⟩ := h.cond c hy,
  let s : CompHaus.of punit ⟶ P1 f (h.large c) :=
  terminal.from _ ≫ pullback.lift (pt (π₁ y)) (pt ⟨x, hx⟩) _,
  swap, { ext t, exact hfx.symm },
  refine ⟨s punit.star, _⟩,
  suffices : s ≫ P1_to_P2 f g (h.large c) hfg = terminal.from _ ≫ pt y,
  { exact fun_like.congr_fun this punit.star },
  delta P1_to_P2,
  apply category_theory.limits.pullback.hom_ext,
  { simp only [category.assoc, pullback.lift_fst], refl },
  { exact subsingleton.elim _ _ }
end

lemma of_surjective (hfg : f ≫ g = 0) (hr : id ≤ r)
  (h : ∀ c, function.surjective (P1_to_P2 f g (hr c) hfg)) :
  strongly_exact f g r :=
begin
  suffices H : ∀ (c : ℝ≥0), g ⁻¹' {0} ∩ filtration B c ⊆ f '' filtration A (r c),
  { refine ⟨_, H, hr⟩,
    ext x,
    have := congr_arg (coe_fn : (A ⟶ C) → (A → C)) hfg,
    exact congr_fun this x },
  rintro c y ⟨hy, hyc⟩,
  let t : CompHaus.of punit ⟶ P2 g c :=
  pullback.lift (terminal.from _ ≫ pt ⟨y, hyc⟩) (terminal.from _) _,
  swap, { ext, exact hy },
  obtain ⟨s, hs⟩ := h c (t punit.star),
  let π₂ : P1 f (hr c) ⟶ (Filtration.obj (r c)).obj A := pullback.snd,
  refine ⟨(π₂ s).val, _⟩,
  let P := CompHaus.of punit,
  suffices : terminal.from P ≫ pt s ≫ π₂ ≫ ((Filtration.obj (r c)).map f) =
    terminal.from _ ≫ pt ⟨y, filtration_mono (hr c) hyc⟩,
  { have hs := fun_like.congr_fun this punit.star, exact ⟨(π₂ s).2, congr_arg subtype.val hs⟩ },
  have H : terminal.from P ≫ pt s ≫ P1_to_P2 f g (hr c) hfg = t,
  { apply continuous_map.ext, rintro ⟨⟩, exact hs },
  erw [← pullback.condition, ← P1_to_P2_comp_fst f g (hr c) hfg, category.assoc,
    reassoc_of H, pullback.lift_fst_assoc],
  refl
end

lemma iff_surjective :
  strongly_exact f g r ↔
  ∃ (hfg : f ≫ g = 0) (hr : ∀ c, c ≤ r c),
    ∀ c, function.surjective (P1_to_P2 f g (hr c) hfg) :=
begin
  split,
  { intro h, obtain ⟨hfg, H⟩ := surjective _ _ h, exact ⟨hfg, h.large, H⟩ },
  { rintro ⟨hfg, hr, h⟩, exact of_surjective f g hfg hr h }
end

end strongly_exact

namespace strongly_exact

variables {J : Type u} [small_category J]
variables {A' B' C' : J ⥤ CompHausFiltPseuNormGrp₁.{u}}
variables (f : A' ⟶ B') (g : B' ⟶ C') (r : ℝ≥0 → ℝ≥0) (c : ℝ≥0) (hrc : c ≤ r c)

variables {r c}

@[simps obj obj_obj obj_map map map_app { fully_applied := ff }]
def P1_functor : J ⥤ walking_cospan ⥤ CompHaus.{u} :=
functor.flip $ cospan
  (whisker_left B' (Filtration.map (c_le_rc hrc)))
  (whisker_right f (Filtration.obj (r c)))

@[simps obj obj_obj obj_map map map_app { fully_applied := ff }]
def P2_functor (c : ℝ≥0) : J ⥤ walking_cospan ⥤ CompHaus.{u} :=
functor.flip $ @cospan _ _ _ ((category_theory.functor.const _).obj (⊤_ _)) _
  (whisker_right g (Filtration.obj c))
  { app := λ j, pt (0 : pseudo_normed_group.filtration (C'.obj j) c),
    naturality' := by { intros, ext, exact (C'.map f).map_zero.symm } }

lemma P1_to_P2_nat_trans_aux_1 (hfg : f ≫ g = 0) (X Y : J) (h : X ⟶ Y) (w w') :
  ((P1_functor f hrc ⋙ lim).map h ≫
         lim_map (diagram_iso_cospan ((P1_functor f hrc).obj Y)).hom ≫
           P1_to_P2 (f.app Y) (g.app Y) hrc w ≫
             lim_map
               (𝟙 (cospan ((Filtration.obj c).map (g.app Y)) (pt 0)) ≫
                  (diagram_iso_cospan ((P2_functor g c).obj Y)).inv)) ≫
      limit.π ((P2_functor g c).obj Y) none =
    ((lim_map (diagram_iso_cospan ((P1_functor f hrc).obj X)).hom ≫
            P1_to_P2 (f.app X) (g.app X) hrc w' ≫
              lim_map
                (𝟙 (cospan ((Filtration.obj c).map (g.app X)) (pt 0)) ≫
                   (diagram_iso_cospan ((P2_functor g c).obj X)).inv)) ≫
         (P2_functor g c ⋙ lim).map h) ≫
      limit.π ((P2_functor g c).obj Y) none :=
begin
  dsimp [P1_to_P2],
  simp only [iso.refl_hom, iso.refl_inv, nat_trans.comp_app, eq_to_iso_refl,
    category.id_comp, category.assoc,
    cones.postcompose_obj_π, lim_map_π_assoc, limit.lift_π,
    diagram_iso_cospan_hom_app, diagram_iso_cospan_inv_app,
    pullback_cone.mk_π_app_one, limit.lift_map],
  dsimp,
  simp only [←(Filtration.obj c).map_comp, category.comp_id, category.id_comp,
    nat_trans.naturality],
end

lemma P1_to_P2_nat_trans_aux_2 (hfg : f ≫ g = 0) (X Y : J) (h : X ⟶ Y) (w w') :
  ((P1_functor f hrc ⋙ lim).map h ≫
         lim_map (diagram_iso_cospan ((P1_functor f hrc).obj Y)).hom ≫
           P1_to_P2 (f.app Y) (g.app Y) hrc w ≫
             lim_map
               (𝟙 (cospan ((Filtration.obj c).map (g.app Y)) (pt 0)) ≫
                  (diagram_iso_cospan ((P2_functor g c).obj Y)).inv)) ≫
      limit.π ((P2_functor g c).obj Y) (some walking_pair.left) =
    ((lim_map (diagram_iso_cospan ((P1_functor f hrc).obj X)).hom ≫
            P1_to_P2 (f.app X) (g.app X) hrc w' ≫
              lim_map
                (𝟙 (cospan ((Filtration.obj c).map (g.app X)) (pt 0)) ≫
                   (diagram_iso_cospan ((P2_functor g c).obj X)).inv)) ≫
         (P2_functor g c ⋙ lim).map h) ≫
      limit.π ((P2_functor g c).obj Y) (some walking_pair.left) :=
begin
  dsimp [P1_to_P2],
  simp only [iso.refl_hom ,iso.refl_inv, eq_to_iso_refl, nat_trans.comp_app,
    category.id_comp, category.assoc, pullback_cone.mk_π_app_left,
    cones.postcompose_obj_π, lim_map_π_assoc, limit.lift_π, limit.lift_map,
    diagram_iso_cospan_hom_app, diagram_iso_cospan_inv_app],
  dsimp,
  simp only [category.comp_id, category.id_comp],
end

lemma P1_to_P2_nat_trans_aux_3 (hfg : f ≫ g = 0) (X Y : J) (h : X ⟶ Y) (w w') :
  ((P1_functor f hrc ⋙ lim).map h ≫
         lim_map (diagram_iso_cospan ((P1_functor f hrc).obj Y)).hom ≫
           P1_to_P2 (f.app Y) (g.app Y) hrc w ≫
             lim_map
               (𝟙 (cospan ((Filtration.obj c).map (g.app Y)) (pt 0)) ≫
                  (diagram_iso_cospan ((P2_functor g c).obj Y)).inv)) ≫
      limit.π ((P2_functor g c).obj Y) (some walking_pair.right) =
    ((lim_map (diagram_iso_cospan ((P1_functor f hrc).obj X)).hom ≫
            P1_to_P2 (f.app X) (g.app X) hrc w' ≫
              lim_map
                (𝟙 (cospan ((Filtration.obj c).map (g.app X)) (pt 0)) ≫
                   (diagram_iso_cospan ((P2_functor g c).obj X)).inv)) ≫
         (P2_functor g c ⋙ lim).map h) ≫
      limit.π ((P2_functor g c).obj Y) (some walking_pair.right) :=
begin
  dsimp [P1_to_P2],
  simp only [category.id_comp, category.assoc, eq_to_iso_refl, iso.refl_inv, nat_trans.comp_app,
    pullback_cone.mk_π_app_right, cones.postcompose_obj_π, limit.lift_π, limit.lift_map,
    diagram_iso_cospan_inv_app, eq_iff_true_of_subsingleton],
end

def P1_to_P2_nat_trans (hfg : f ≫ g = 0) :
  (P1_functor f hrc ⋙ lim) ⟶ (P2_functor g c ⋙ lim) :=
{ app := λ j, begin
    refine _ ≫ P1_to_P2 (f.app j) (g.app j) hrc (by { rw [← nat_trans.comp_app, hfg], refl }) ≫ _,
    { refine lim_map (diagram_iso_cospan _).hom, },
    { refine lim_map (_ ≫ (diagram_iso_cospan _).inv), exact 𝟙 _, }
  end,
  naturality' := λ X Y h, begin
    -- It would be nicer to use `pullback.hom_ext` here, but it doesn't unify.
    -- Nevertheless, we can bash out the remaining goals with `simp`.
    apply limit.hom_ext, rintros (⟨⟩|⟨⟨⟩⟩),
    { apply P1_to_P2_nat_trans_aux_1 _ _ _ hfg, },
    { apply P1_to_P2_nat_trans_aux_2 _ _ _ hfg, },
    { apply P1_to_P2_nat_trans_aux_3 _ _ _ hfg, },
  end }

attribute [simps] P1_to_P2_nat_trans

set_option pp.universes true

/-
TODO:

jmc: below is a framework for setting up some canonical isomorphisms between limits.
It really boils down to saying that limits commute.
This shouldn't be so hard...
I'm not convinced that this is the best way to do it,
there should be a more ergonomic approach.

scott: I've replaced the definition of `P1_iso`
with one that uses the general theory for commuting limits.
-/

instance (c : ℝ≥0) : preserves_limits (Filtration.obj c) :=
by { dsimp [Filtration], apply_instance, }

def P1_iso {A B : Fintype.{u} ⥤ CompHausFiltPseuNormGrp₁.{u}}
  (f : A ⟶ B) {r : ℝ≥0 → ℝ≥0} {c : ℝ≥0} (hrc : c ≤ r c) (S : Profinite) :
  P1.{u} ((Profinite.extend_nat_trans.{u u+1} f).app S) hrc ≅
    limit (P1_functor.{u} (whisker_left S.fintype_diagram f) hrc ⋙ lim) :=
begin
  refine has_limit.iso_of_nat_iso (_ ≪≫ (cospan_comp_iso _ _ _).symm) ≪≫
    (limit_flip_comp_lim_iso_limit_comp_lim' _).symm,

  -- This next line can be removed later if/when we generalize universe parameters in finite (co)limits
  refine _ ≪≫ (diagram_iso_cospan _).symm,

  refine cospan_ext (preserves_limit_iso _ _) (preserves_limit_iso _ _) (preserves_limit_iso _ _)
    (by { apply limit.hom_ext, intros, ext, simp, })
    (begin
      apply limit.hom_ext,
      intros,
      simp [-category_theory.functor.map_comp, ←(Filtration.obj (r c)).map_comp],
    end)
end

open category_theory.limits

def P2_iso {B C : Fintype.{u} ⥤ CompHausFiltPseuNormGrp₁.{u}}
  (g : B ⟶ C) (c : ℝ≥0) (S : Profinite) :
  P2.{u} ((Profinite.extend_nat_trans.{u u+1} g).app S) c ≅
    limit (P2_functor.{u} (whisker_left S.fintype_diagram g) c ⋙ lim) :=
begin
  refine has_limit.iso_of_nat_iso (_ ≪≫ (cospan_comp_iso _ _ _).symm) ≪≫
    (limit_flip_comp_lim_iso_limit_comp_lim' _).symm,

  -- This next line can be removed later if/when we generalize universe parameters in finite (co)limits
  refine _ ≪≫ (diagram_iso_cospan _).symm,

  refine cospan_ext _ _ _ _ _,
  exact (preserves_limit_iso _ _),
  exact category_theory.limits.limit_const_terminal.symm,
  exact (preserves_limit_iso _ _),
  { apply limit.hom_ext, intros, simp [-category_theory.functor.map_comp, ←(Filtration.obj c).map_comp], },
  { apply limit.hom_ext, intros, ext, simp, },
end

-- move me, generalize
lemma extend_aux {A₁ B₁ A₂ B₂ : CompHaus}
  (e₁ : A₁ ≅ B₁) (e₂ : A₂ ≅ B₂) (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) (hf : epi f)
  (H : e₁.inv ≫ f ≫ e₂.hom = g) :
  epi g :=
by { subst H, apply epi_comp _ _, apply_instance, apply epi_comp }

-- move me, generalize
lemma extend_aux' {A₁ B₁ A₂ B₂ : CompHaus}
  (e₁ : A₁ ≅ B₁) (e₂ : A₂ ≅ B₂) (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) (hf : epi f)
  (H : f = e₁.hom ≫ g ≫ e₂.inv) :
  epi g :=
by { rw [← iso.inv_comp_eq, iso.eq_comp_inv, category.assoc] at H, apply extend_aux e₁ e₂ f g hf H }

lemma extend_aux_1 {A B C : Fintype.{u} ⥤ CompHausFiltPseuNormGrp₁.{u}} {r : ℝ≥0 → ℝ≥0} {c : ℝ≥0}
  (S : Profinite.{u}) (f : A ⟶ B) (g : B ⟶ C) (hrc : c ≤ r c) (w w') :
  ((P1_iso.{u} f hrc S).symm.inv ≫
         lim_map.{u u u u+1}
             (P1_to_P2_nat_trans.{u}
                (whisker_left.{u u u+1 u u+1 u} S.fintype_diagram f)
                (whisker_left.{u u u+1 u u+1 u} S.fintype_diagram g) hrc w) ≫
           (P2_iso.{u} g c S).symm.hom) ≫
      pullback.fst.{u u+1} =
    P1_to_P2.{u} ((Profinite.extend_nat_trans.{u u+1} f).app S)
        ((Profinite.extend_nat_trans.{u u+1} g).app S) hrc w' ≫
      pullback.fst.{u u+1} :=
begin
  apply (cancel_mono ((preserves_limit_iso (Filtration.obj _) _).hom)).1,
  apply limit.hom_ext,
  { -- TODO this is not the prettiest proof.
    -- We need some good simp lemmas for `P1_iso`, `P2_iso`, and `P1_to_P2`.
    intro j,
    simp only [P1_to_P2_comp_fst, category_theory.preserves_limits_iso_hom_π, category_theory.category.assoc],
    dsimp [P2_iso],
    simp only [category_theory.iso.symm_inv,
      category_theory.limits.cospan_ext_inv_app_left,
      category_theory.iso.trans_inv,
      category_theory.nat_trans.comp_app,
      category_theory.category.id_comp,
      category_theory.preserves_limits_iso_inv_π,
      category_theory.limits.cospan_comp_iso_hom_app_left,
      category_theory.category.assoc,
      category_theory.limits.has_limit.iso_of_nat_iso_inv_π_assoc],
    erw [limit_flip_comp_lim_iso_limit_comp_lim'_hom_π_π, lim_map_π_assoc],
    simp only [category_theory.category.id_comp,
      CompHausFiltPseuNormGrp₁.strongly_exact.P1_to_P2_nat_trans_app,
      category_theory.category.assoc],
    erw [lim_map_π],
    dsimp [P1_to_P2],
    simp only [category_theory.category.comp_id,
      category_theory.iso.refl_hom,
      category_theory.eq_to_iso_refl,
      category_theory.limits.lim_map_π,
      category_theory.limits.diagram_iso_cospan_hom_app,
      category_theory.limits.pullback.lift_fst],
    dsimp [P1_iso],
    simp only [category_theory.category.assoc],
    erw [limit_flip_comp_lim_iso_limit_comp_lim'_inv_π_π],
    simp only [category_theory.limits.has_limit.iso_of_nat_iso_hom_π_assoc,
      category_theory.nat_trans.comp_app,
      category_theory.iso.symm_hom,
      category_theory.limits.cospan_comp_iso_inv_app_left,
      category_theory.category.assoc,
      category_theory.iso.trans_hom,
      category_theory.limits.cospan_ext_hom_app_left],
    dsimp,
    simp only [category_theory.preserves_limits_iso_hom_π, category_theory.category.id_comp], },
  all_goals { apply_instance, },
end

lemma extend {A B C : Fintype.{u} ⥤ CompHausFiltPseuNormGrp₁.{u}}
  (f : A ⟶ B) (g : B ⟶ C) (r : ℝ≥0 → ℝ≥0)
  (hfg : ∀ S, strongly_exact (f.app S) (g.app S) r) (S : Profinite) :
  strongly_exact
    ((Profinite.extend_nat_trans f).app S) ((Profinite.extend_nat_trans g).app S) r :=
begin
  have hr : id ≤ r := (hfg $ Fintype.of punit).large,
  rw strongly_exact.iff_surjective,
  refine ⟨_, hr, _⟩,
  { rw [← nat_trans.comp_app, ← Profinite.extend_nat_trans_comp],
    apply limit.hom_ext,
    intro X,
    specialize hfg (S.fintype_diagram.obj X),
    erw [zero_comp, limit.lift_π],
    simp only [cones.postcompose_obj_π, whisker_left_comp, nat_trans.comp_app,
      limit.cone_π, whisker_left_app, hfg.comp_eq_zero, comp_zero], },
  intros c,
  have hfg' : whisker_left.{u u u+1 u u+1 u} S.fintype_diagram f ≫
    whisker_left.{u u u+1 u u+1 u} S.fintype_diagram g = 0,
  { ext X : 2,
    simp only [nat_trans.comp_app, whisker_left_app, (hfg (S.fintype_diagram.obj X)).comp_eq_zero],
    refl },
  have key := CompHaus.is_limit.surjective_of_surjective'
    (P1_functor.{u} (whisker_left S.fintype_diagram f) (hr c) ⋙ lim)
    (P2_functor.{u} (whisker_left S.fintype_diagram g) c ⋙ lim)
    (P1_to_P2_nat_trans _ _ _ hfg') _,
  swap,
  { intro X, specialize hfg (S.fintype_diagram.obj X), rw [iff_surjective] at hfg,
    rcases hfg with ⟨aux', hr, hfg⟩, specialize hfg c,
    rw ← CompHaus.epi_iff_surjective at hfg ⊢,
    apply_with epi_comp {instances := ff},
    { show epi ((@limits.lim _ _ _ _ _).map _), apply_instance, },
    apply_with epi_comp {instances := ff},
    { exact hfg },
    { show epi ((@limits.lim _ _ _ _ _).map _), apply_instance, }, },
  rw ← CompHaus.epi_iff_surjective at key ⊢,
  refine extend_aux (P1_iso f (hr c) S).symm (P2_iso g c S).symm _ _ key _,
  apply pullback.hom_ext,
  apply extend_aux_1,
  apply subsingleton.elim,
end

end strongly_exact

instance has_zero_nat_trans_CHFPNG₁ {𝒞 : Type*} [category 𝒞]
  (A B : 𝒞 ⥤ CompHausFiltPseuNormGrp₁.{u}) :
  has_zero (A ⟶ B) :=
⟨⟨0, λ S T f, by { ext t, exact (B.map f).map_zero.symm }⟩⟩

@[simp] lemma zero_app {𝒞 : Type*} [category 𝒞] (A B : 𝒞 ⥤ CompHausFiltPseuNormGrp₁.{u}) (S) :
  (0 : A ⟶ B).app S = 0 := rfl

@[simp] lemma Profinite.extend_nat_trans_zero (A B : Fintype ⥤ CompHausFiltPseuNormGrp₁.{u}) :
  Profinite.extend_nat_trans (0 : A ⟶ B) = 0 :=
begin
  apply Profinite.extend_nat_trans_ext,
  rw [Profinite.extend_nat_trans_whisker_left],
  ext S : 2,
  simp only [nat_trans.comp_app, whisker_left_app, zero_app, zero_comp, comp_zero],
end

lemma strongly_exact_extend_zero_left (A B C : Fintype ⥤ CompHausFiltPseuNormGrp₁.{u})
  (g : B ⟶ C) (r : ℝ≥0 → ℝ≥0)
  (hfg : ∀ S, strongly_exact (0 : A.obj S ⟶ B.obj S) (g.app S) r) (S : Profinite) :
  strongly_exact (0 : (Profinite.extend A).obj S ⟶ (Profinite.extend B).obj S)
    ((Profinite.extend_nat_trans g).app S) r :=
begin
  have := strongly_exact.extend (0 : A ⟶ B) g r hfg S,
  simpa,
end

lemma strongly_exact_extend_zero_right (A B C : Fintype ⥤ CompHausFiltPseuNormGrp₁.{u})
  (f : A ⟶ B) (r : ℝ≥0 → ℝ≥0)
  (hfg : ∀ S, strongly_exact (f.app S) (0 : B.obj S ⟶ C.obj S) r) (S : Profinite) :
  strongly_exact ((Profinite.extend_nat_trans f).app S)
    (0 : (Profinite.extend B).obj S ⟶ (Profinite.extend C).obj S) r :=
begin
  have := strongly_exact.extend f (0 : B ⟶ C) r hfg S,
  simpa,
end

variables (C)

lemma strongly_exact_of_epi (f : A ⟶ B) (r : ℝ≥0 → ℝ≥0) (hr : id ≤ r)
  (hf : ∀ c, filtration B c ⊆ f '' (filtration A (r c))) :
  strongly_exact f (0 : B ⟶ C) r :=
begin
  refine ⟨_, _, hr⟩,
  { rw comp_zero },
  { intro c, exact set.subset.trans (set.inter_subset_right _ _) (hf c), }
end

variables (A) {C}

lemma strongly_exact_of_mono (g : B ⟶ C) [hg : mono ((to_PNG₁ ⋙ PseuNormGrp₁.to_Ab).map g)] :
  strongly_exact (0 : A ⟶ B) g id :=
begin
  refine ⟨_, _, le_rfl⟩,
  { rw zero_comp },
  { rintro c x ⟨hx, -⟩,
    suffices : x = 0, { subst x, refine ⟨0, zero_mem_filtration _, rfl⟩, },
    simp only [set.mem_preimage, set.mem_singleton_iff] at hx,
    rw [AddCommGroup.mono_iff_injective, injective_iff_map_eq_zero] at hg,
    exact hg _ hx, }
end

end CompHausFiltPseuNormGrp₁

namespace Condensed

open CompHausFiltPseuNormGrp₁

lemma zero_iff_ExtrDisc {A B : Condensed.{u} Ab.{u+1}} (f : A ⟶ B) :
  f = 0 ↔ (∀ S : ExtrDisc, f.val.app (op S.val) = 0) :=
begin
  split,
  { rintros ⟨rfl⟩, simp },
  { intros h,
    apply (Condensed_ExtrSheafProd_equiv Ab).functor.map_injective,
    apply (ExtrSheafProd_to_presheaf Ab).map_injective,
    ext : 2,
    apply h }
end

lemma exact_iff_ExtrDisc {A B C : Condensed.{u} Ab.{u+1}} (f : A ⟶ B) (g : B ⟶ C) :
  exact f g ↔ ∀ (S : ExtrDisc),
    exact (f.1.app $ ExtrDisc_to_Profinite.op.obj (op S))
          (g.1.app $ ExtrDisc_to_Profinite.op.obj (op S)) :=
begin
  simp only [abelian.exact_iff, zero_iff_ExtrDisc, forall_and_distrib],
  refine and_congr iff.rfl _,
  apply forall_congr,
  intro S,
  symmetry,
  rw [← cancel_epi (kernel_iso g S).hom,
    ← cancel_mono (cokernel_iso f S).hom],
  dsimp only [functor.op_obj, ExtrDisc_to_Profinite_obj],
  simp only [category.assoc, zero_comp, comp_zero],
  erw [kernel_iso_hom_assoc, cokernel_iso_hom],
  exact iff.rfl,
end

open comphaus_filtered_pseudo_normed_group
open CompHausFiltPseuNormGrp₁.strongly_exact (P1 P2 P1_to_P2 P1_to_P2_comp_fst c_le_rc)

lemma exact_of_strongly_exact {A B C : CompHausFiltPseuNormGrp₁.{u}}
  (f : A ⟶ B) (g : B ⟶ C) (r : ℝ≥0 → ℝ≥0)
  (hfg : strongly_exact f g r) :
  exact (to_Condensed.map f) (to_Condensed.map g) :=
begin
  rw exact_iff_ExtrDisc,
  intro S,
  rw strongly_exact.iff_surjective at hfg,
  rcases hfg with ⟨hfg, hr, H⟩,
  simp only [subtype.val_eq_coe, to_Condensed_map, CompHausFiltPseuNormGrp.Presheaf.map_app,
    whisker_right_app, Ab.exact_ulift_map],
  rw AddCommGroup.exact_iff',
  split,
  { show @CompHausFiltPseuNormGrp.presheaf.map.{u}
      (CHFPNG₁_to_CHFPNGₑₗ.obj A) (CHFPNG₁_to_CHFPNGₑₗ.obj C)
      (@strict_comphaus_filtered_pseudo_normed_group_hom.to_chfpsng_hom.{u u} A C _ _ (f ≫ g))
      (unop.{u+2} (ExtrDisc_to_Profinite.{u}.op.obj (op S))) = 0,
    rw hfg, ext x s, refl, },
  { rintro ⟨_, c, y₀ : S.val → filtration B c, hy₀, rfl⟩ hy,
    dsimp at hy ⊢,
    let y : CompHaus.of S.val ⟶ (Filtration.obj c).obj B := ⟨y₀, hy₀⟩,
    let t : CompHaus.of S.val ⟶ P2 g c := pullback.lift y (terminal.from _) _,
    swap,
    { apply continuous_map.ext, intros a, apply subtype.ext,
      simp only [add_monoid_hom.mem_ker, CompHausFiltPseuNormGrp.presheaf.map_apply] at hy,
      have := congr_arg subtype.val hy,
      exact congr_fun this a },
    let s := ExtrDisc.lift' _ (H c) t,
    have hs : s ≫ P1_to_P2 f g (hr c) hfg = t := ExtrDisc.lift_lifts' _ _ _,
    let π₂ : P1 f (hr c) ⟶ (Filtration.obj (r c)).obj A := pullback.snd,
    let x₀ := (s ≫ π₂).1,
    have hx₀ := (s ≫ π₂).2,
    refine ⟨⟨_, _, x₀, hx₀, rfl⟩, _⟩,
    apply_fun (λ φ, φ ≫ pullback.fst) at hs,
    erw [pullback.lift_fst y (terminal.from _)] at hs,
    rw [category.assoc, P1_to_P2_comp_fst, ← cancel_mono ((Filtration.map (c_le_rc (hr c))).app B),
      category.assoc, pullback.condition] at hs,
    ext z,
    have := fun_like.congr_fun hs z,
    exact congr_arg subtype.val this, }
end
.

section move_this

-- generalize to faithful additive functors
-- (and show that `Ab.ulift` is an instance)
@[simp]
lemma _root_.Ab.ulift.map_eq_zero_iff {A B : Ab} (f : A ⟶ B) :
  (Ab.ulift.{v}).map f = 0 ↔ f = 0 :=
begin
  split, swap, { rintro rfl, refl },
  intro h,
  ext x,
  have := congr_hom h ⟨x⟩,
  exact congr_arg ulift.down this
end

end move_this

-- move this
constant StoneCech : Type u ⥤ ExtrDisc.{u}

lemma strongly_exact_of_exact_aux {A B C : CompHausFiltPseuNormGrp₁.{u}}
  (f : A ⟶ B) (g : B ⟶ C) (hfg : exact (to_Condensed.map f) (to_Condensed.map g)) (c : ℝ≥0) :
  ∃ c', g ⁻¹' {0} ∩ (filtration B c) ⊆ f '' (filtration A c') :=
begin
  rw exact_iff_ExtrDisc at hfg,
  let S := StoneCech.obj (g ⁻¹' {0} ∩ (filtration B c) : set B),
  specialize hfg S,
  dsimp at hfg,
  simp only [Ab.exact_ulift_map] at hfg,
  rw AddCommGroup.exact_iff at hfg,
  let α : (CompHausFiltPseuNormGrp.of B).presheaf S.val :=
  sorry,
  sorry
end

lemma exact_iff_strongly_exact {A B C : CompHausFiltPseuNormGrp₁.{u}}
  (f : A ⟶ B) (g : B ⟶ C) :
  exact (to_Condensed.map f) (to_Condensed.map g) ↔
    ∃ r, strongly_exact f g r :=
begin
  split, swap,
  { rintro ⟨r, hfg⟩, exact exact_of_strongly_exact f g r hfg },
  intro hfg,
  have : ∀ c : ℝ≥0, ∃ c', g ⁻¹' {0} ∩ (filtration B c) ⊆ f '' (filtration A c'),
    from strongly_exact_of_exact_aux f g hfg,
  choose r' h' using this,
  refine ⟨r' ⊔ id, ⟨_, _, le_sup_right⟩⟩,
  { rw exact_iff_ExtrDisc at hfg,
    haveI : projective (Profinite.of punit.{u+1}) := sorry,
    have H := (hfg (ExtrDisc.of (Profinite.of $ punit))).w,
    dsimp at H,
    rw [← functor.map_comp, _root_.Ab.ulift.map_eq_zero_iff] at H,
    ext x,
    obtain ⟨c, hc⟩ := exhaustive _ x,
    have aux := congr_hom H ⟨function.const _ x, ⟨c, λ _, ⟨x, hc⟩, _⟩⟩,
    have := congr_fun (congr_arg subtype.val aux) punit.star, exact this,
    refine ⟨continuous_const, rfl⟩ },
  { intros c,
    refine subset_trans (h' c) (set.image_subset _ _),
    refine filtration_mono le_sup_left }
end


@[simp] lemma to_Condensed_map_zero (A B : CompHausFiltPseuNormGrp₁.{u}) :
  to_Condensed.map (0 : A ⟶ B) = 0 :=
by { ext S s x, refl, }

lemma mono_to_Condensed_map {A B : CompHausFiltPseuNormGrp₁.{u}}
  (f : A ⟶ B) (hf : strongly_exact (0 : A ⟶ A) f id) :
  mono (to_Condensed.map f) :=
begin
  refine ((abelian.tfae_mono (to_Condensed.obj A) (to_Condensed.map f)).out 2 0).mp _,
  have := exact_of_strongly_exact (0 : A ⟶ A) f id hf,
  simpa only [to_Condensed_map_zero],
end

lemma epi_to_Condensed_map {A B : CompHausFiltPseuNormGrp₁.{u}}
  (f : A ⟶ B) (r : ℝ≥0 → ℝ≥0) (hf : strongly_exact f (0 : B ⟶ B) r) :
  epi (to_Condensed.map f) :=
begin
  refine ((abelian.tfae_epi (to_Condensed.obj B) (to_Condensed.map f)).out 2 0).mp _,
  have := exact_of_strongly_exact f (0 : B ⟶ B) r hf,
  simpa only [to_Condensed_map_zero]
end

end Condensed
