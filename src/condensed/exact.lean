import for_mathlib.Profinite.extend
import for_mathlib.AddCommGroup.exact

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

def diagram_of_pt (y : cG.X) : J ⥤ CompHaus.{u} :=
{ obj := λ j, pullback (α.app j) (pt y ≫ cG.π.app j),
  map := λ i j f, pullback.lift (pullback.fst ≫ F.map f) pullback.snd
    (by rw [category.assoc, α.naturality, pullback.condition_assoc, category.assoc, cG.w]),
  map_id' := sorry,
  map_comp' := sorry }

def cone_of_pt (y : cG.X) : cone (diagram_of_pt F G α cG y) :=
{ X := pullback (hcG.map cF α) (pt y),
  π :=
  { app := λ j, pullback.lift
      (pullback.fst ≫ cF.π.app _)
      pullback.snd
      (by rw [category.assoc, ← pullback.condition_assoc, is_limit.map_π]),
    naturality' := sorry } }

def is_limit_cone_of_pt (y : cG.X) : is_limit (cone_of_pt F G α cF cG hcG y) :=
{ lift := λ S, pullback.lift
    (hcF.lift ⟨S.X,
    { app := λ j, S.π.app j ≫ pullback.fst,
      naturality' := sorry }⟩)
    (terminal.from _)
    sorry,
  fac' := sorry,
  uniq' := sorry }

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
  let ee : E' ≅ Top.limit_cone _ :=
    hE'.unique_up_to_iso (Top.limit_cone_is_limit _),
  let e : E'.X ≅ (Top.limit_cone _).X :=
    hE'.cone_point_unique_up_to_iso (Top.limit_cone_is_limit _),
  haveI : ∀ j : J, t2_space (((diagram_of_pt F G α cG y ⋙ CompHaus_to_Top).obj j)),
  { intros j,
    change t2_space ((diagram_of_pt F G α cG y).obj j), apply_instance },
  haveI : ∀ j : J, compact_space (((diagram_of_pt F G α cG y ⋙ CompHaus_to_Top).obj j)),
  { intros j,
    change compact_space ((diagram_of_pt F G α cG y).obj j), apply_instance },
  haveI : ∀ j : J, nonempty (((diagram_of_pt F G α cG y ⋙ CompHaus_to_Top).obj j)),
  { -- use hα,
    sorry },
  have := Top.nonempty_limit_cone_of_compact_t2_cofiltered_system
    (diagram_of_pt F G α cG y ⋙ CompHaus_to_Top),
  obtain ⟨a⟩ := this,
  let b := e.inv a,
  use pt b,
  sorry
end

end CompHaus

namespace CompHausFiltPseuNormGrp₁

variables {A B C : CompHausFiltPseuNormGrp₁.{u}}

structure exact_with_constant (f : A ⟶ B) (g : B ⟶ C) (r : ℝ≥0) : Prop :=
(comp_eq_zero : f ≫ g = 0)
(cond : ∀ c : ℝ≥0, g ⁻¹' {0} ∩ (filtration B c) ⊆ f '' (filtration A (r * c)))

lemma exact_with_constant.exact {f : A ⟶ B} {g : B ⟶ C} {r : ℝ≥0} (h : exact_with_constant f g r) :
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

-- move this
@[simps obj_obj obj_map_to_fun map_app {fully_applied := ff}]
def Filtration : ℝ≥0 ⥤ CompHausFiltPseuNormGrp₁.{u} ⥤ CompHaus.{u} :=
{ obj := λ c,
  { obj := λ M, CompHaus.of (pseudo_normed_group.filtration M c),
    map := λ M N f, ⟨f.level, f.level_continuous c⟩,
    map_id' := by { intros, ext, refl },
    map_comp' := by { intros, ext, refl } },
  map := λ c₁ c₂ h,
  { app := λ M, ⟨@pseudo_normed_group.cast_le _ _ c₁ c₂ ⟨h.le⟩,
      @comphaus_filtered_pseudo_normed_group.continuous_cast_le _ _ c₁ c₂ ⟨h.le⟩⟩ },
  map_id' := by { intros, ext, refl },
  map_comp' := by { intros, ext, refl } }
.

instance mono_Filtration_map_app (c₁ c₂ : ℝ≥0) (h : c₁ ⟶ c₂) (M) :
  mono ((Filtration.map h).app M) :=
by { rw CompHaus.mono_iff_injective, convert injective_cast_le _ _ }

namespace exact_with_constant
noncomputable theory

variables (f : A ⟶ B) (g : B ⟶ C) (r c : ℝ≥0) [fact (1 ≤ r)]

def c_le_rc : c ⟶ r * c := hom_of_le $ fact.out _

/-- Given `f : A ⟶ B`, `P1` is the pullback `B_c ×_{B_{rc}} A_{rc}`. -/
def P1 : CompHaus :=
pullback ((Filtration.map (c_le_rc r c)).app B) ((Filtration.obj (r * c)).map f)

def pt {X : CompHaus} (x : X) : (⊤_ CompHaus) ⟶ X :=
⟨λ _, x, continuous_const⟩

/-- Given `g : B ⟶ C`, `P2` is the pullback `B_c ×_{C_c} {pt}`. -/
def P2 : CompHaus :=
pullback ((Filtration.obj c).map g) (pt (0 : pseudo_normed_group.filtration C c))

def P1_to_P2 (hfg : f ≫ g = 0) : P1 f r c ⟶ P2 g c :=
pullback.lift pullback.fst (terminal.from _)
begin
  rw [← cancel_mono ((Filtration.map (c_le_rc r c)).app C), category.assoc,
    nat_trans.naturality, pullback.condition_assoc, ← functor.map_comp, hfg],
  refl,
end

lemma P1_to_P2_comp_fst (hfg : f ≫ g = 0) :
  P1_to_P2 f g r c hfg ≫ pullback.fst = pullback.fst :=
pullback.lift_fst _ _ _

lemma surjective (h : exact_with_constant f g r) :
  ∃ (h : f ≫ g = 0), ∀ c, function.surjective (P1_to_P2 f g r c h) :=
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
  let s : CompHaus.of punit ⟶ P1 f r c :=
  terminal.from _ ≫ pullback.lift (pt (π₁ y)) (pt ⟨x, hx⟩) _,
  swap, { ext t, exact hfx.symm },
  refine ⟨s punit.star, _⟩,
  suffices : s ≫ P1_to_P2 f g r c hfg = terminal.from _ ≫ pt y,
  { exact fun_like.congr_fun this punit.star },
  delta P1_to_P2,
  apply category_theory.limits.pullback.hom_ext,
  { simp only [category.assoc, pullback.lift_fst], refl },
  { exact subsingleton.elim _ _ }
end

lemma of_surjective (hfg : f ≫ g = 0) (h : ∀ c, function.surjective (P1_to_P2 f g r c hfg)) :
  exact_with_constant f g r :=
begin
  have H : ∀ (c : ℝ≥0), g ⁻¹' {0} ∩ filtration B c ⊆ f '' filtration A (r * c),
  { rintro c y ⟨hy, hyc⟩,
    let t : CompHaus.of punit ⟶ P2 g c :=
    pullback.lift (terminal.from _ ≫ pt ⟨y, hyc⟩) (terminal.from _) _,
    swap, { ext, exact hy },
    obtain ⟨s, hs⟩ := h c (t punit.star),
    let π₂ : P1 f r c ⟶ (Filtration.obj (r * c)).obj A := pullback.snd,
    refine ⟨(π₂ s).val, _⟩,
    let P := CompHaus.of punit,
    suffices : terminal.from P ≫ pt s ≫ π₂ ≫ ((Filtration.obj (r*c)).map f) =
      terminal.from _ ≫ pt ⟨y, filtration_mono (fact.out _) hyc⟩,
    { have hs := fun_like.congr_fun this punit.star, exact ⟨(π₂ s).2, congr_arg subtype.val hs⟩ },
    have H : terminal.from P ≫ pt s ≫ P1_to_P2 f g r c hfg = t,
    { apply continuous_map.ext, rintro ⟨⟩, exact hs },
    rw [← pullback.condition, ← P1_to_P2_comp_fst f g r c hfg, category.assoc,
      reassoc_of H, pullback.lift_fst_assoc],
    refl },
  refine ⟨_, H⟩,
  ext x,
  have := congr_arg (coe_fn : (A ⟶ C) → (A → C)) hfg,
  exact congr_fun this x,
end

lemma iff_surjective :
  exact_with_constant f g r ↔
  ∃ (h : f ≫ g = 0), ∀ c, function.surjective (P1_to_P2 f g r c h) :=
begin
  split,
  { exact surjective _ _ _ },
  { rintro ⟨hfg, h⟩, exact of_surjective f g r hfg h }
end

end exact_with_constant

-- move this
instance : has_zero_morphisms (CompHausFiltPseuNormGrp₁.{u}) :=
{ has_zero := λ M₁ M₂, ⟨0⟩,
  comp_zero' := λ _ _ f _, rfl,
  zero_comp' := λ _ _ _ f, by { ext, exact f.map_zero } }

lemma exact_with_constant_extend {A B C : Fintype ⥤ CompHausFiltPseuNormGrp₁.{u}}
  (f : A ⟶ B) (g : B ⟶ C) (r : ℝ≥0) [fact (1 ≤ r)]
  (hfg : ∀ S, exact_with_constant (f.app S) (g.app S) r) (S : Profinite) :
  exact_with_constant
    ((Profinite.extend_nat_trans f).app S) ((Profinite.extend_nat_trans g).app S) r :=
begin
  rw exact_with_constant.iff_surjective,
  fsplit,
  { rw [← nat_trans.comp_app, ← Profinite.extend_nat_trans_comp],
    apply limit.hom_ext,
    intro X,
    specialize hfg (S.fintype_diagram.obj X),
    erw [zero_comp, limit.lift_π],
    simp only [cones.postcompose_obj_π, whisker_left_comp, nat_trans.comp_app,
      limit.cone_π, whisker_left_app, hfg.comp_eq_zero, comp_zero], },
  intros c,
  sorry
end

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

lemma exact_with_constant_extend_zero_left (A B C : Fintype ⥤ CompHausFiltPseuNormGrp₁.{u})
  (g : B ⟶ C) (r : ℝ≥0) [fact (1 ≤ r)]
  (hfg : ∀ S, exact_with_constant (0 : A.obj S ⟶ B.obj S) (g.app S) r) (S : Profinite) :
  exact_with_constant (0 : (Profinite.extend A).obj S ⟶ (Profinite.extend B).obj S)
    ((Profinite.extend_nat_trans g).app S) r :=
begin
  have := exact_with_constant_extend (0 : A ⟶ B) g r hfg S,
  simpa,
end

lemma exact_with_constant_extend_zero_right (A B C : Fintype ⥤ CompHausFiltPseuNormGrp₁.{u})
  (f : A ⟶ B) (r : ℝ≥0) [fact (1 ≤ r)]
  (hfg : ∀ S, exact_with_constant (f.app S) (0 : B.obj S ⟶ C.obj S) r) (S : Profinite) :
  exact_with_constant ((Profinite.extend_nat_trans f).app S)
    (0 : (Profinite.extend B).obj S ⟶ (Profinite.extend C).obj S) r :=
begin
  have := exact_with_constant_extend f (0 : B ⟶ C) r hfg S,
  simpa,
end

variables (C)

lemma exact_with_constant_of_epi (f : A ⟶ B) [H : epi ((to_PNG₁ ⋙ PseuNormGrp₁.to_Ab).map f)]
  (r : ℝ≥0) (hf : ∀ c, filtration B c ⊆ f '' (filtration A (r * c))) :
  exact_with_constant f (0 : B ⟶ C) r :=
begin
  fsplit,
  { rw comp_zero },
  { intro c, exact set.subset.trans (set.inter_subset_right _ _) (hf c), }
end

variables (A) {C}

lemma exact_with_constant_of_mono (g : B ⟶ C) [hg : mono ((to_PNG₁ ⋙ PseuNormGrp₁.to_Ab).map g)] :
  exact_with_constant (0 : A ⟶ B) g 1 :=
begin
  fsplit,
  { rw zero_comp },
  { rintro c x ⟨hx, -⟩,
    suffices : x = 0, { subst x, refine ⟨0, zero_mem_filtration _, rfl⟩, },
    simp only [set.mem_preimage, set.mem_singleton_iff] at hx,
    rw [AddCommGroup.mono_iff_injective, add_monoid_hom.injective_iff] at hg,
    exact hg _ hx, }
end

end CompHausFiltPseuNormGrp₁

namespace condensed

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
  rw [← cancel_epi (kernel_iso g S).hom, ← cancel_mono (cokernel_iso f S).hom],
  dsimp only [functor.op_obj, ExtrDisc_to_Profinite_obj],
  simp only [category.assoc, zero_comp, comp_zero],
  erw [kernel_iso_hom_assoc, cokernel_iso_hom],
  exact iff.rfl,
end

open comphaus_filtered_pseudo_normed_group
open CompHausFiltPseuNormGrp₁.exact_with_constant (P1 P2 P1_to_P2 P1_to_P2_comp_fst c_le_rc)

lemma exact_of_exact_with_constant {A B C : CompHausFiltPseuNormGrp₁.{u}}
  (f : A ⟶ B) (g : B ⟶ C) (r : ℝ≥0) (hr : 1 ≤ r)
  (hfg : exact_with_constant f g r) :
  exact (to_Condensed.map f) (to_Condensed.map g) :=
begin
  rw exact_iff_ExtrDisc,
  intro S,
  haveI h1r : fact (1 ≤ r) := ⟨hr⟩,
  rw exact_with_constant.iff_surjective at hfg,
  rcases hfg with ⟨hfg, H⟩,
  simp only [subtype.val_eq_coe, to_Condensed_map, CompHausFiltPseuNormGrp.Presheaf.map_app,
    whisker_right_app, Ab.exact_ulift_map],
  rw AddCommGroup.exact_iff',
  split,
  { show @CompHausFiltPseuNormGrp.presheaf.map.{u}
      (enlarging_functor.obj A) (enlarging_functor.obj C)
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
    have hs : s ≫ P1_to_P2 f g r c hfg = t := ExtrDisc.lift_lifts' _ _ _,
    let π₂ : P1 f r c ⟶ (Filtration.obj (r * c)).obj A := pullback.snd,
    let x₀ := (s ≫ π₂).1,
    have hx₀ := (s ≫ π₂).2,
    refine ⟨⟨_, _, x₀, hx₀, rfl⟩, _⟩,
    apply_fun (λ φ, φ ≫ pullback.fst) at hs,
    erw [pullback.lift_fst y (terminal.from _)] at hs,
    rw [category.assoc, P1_to_P2_comp_fst, ← cancel_mono ((Filtration.map (c_le_rc r c)).app B),
      category.assoc, pullback.condition] at hs,
    ext z,
    have := fun_like.congr_fun hs z,
    exact congr_arg subtype.val this, }
end
.

@[simp] lemma to_Condensed_map_zero (A B : CompHausFiltPseuNormGrp₁.{u}) :
  to_Condensed.map (0 : A ⟶ B) = 0 :=
by { ext S s x, refl, }

lemma mono_to_Condensed_map {A B : CompHausFiltPseuNormGrp₁.{u}}
  (f : A ⟶ B) (hf : exact_with_constant (0 : A ⟶ A) f 1) :
  mono (to_Condensed.map f) :=
begin
  refine ((abelian.tfae_mono (to_Condensed.obj A) (to_Condensed.map f)).out 2 0).mp _,
  have := exact_of_exact_with_constant (0 : A ⟶ A) f 1 le_rfl hf,
  simpa only [to_Condensed_map_zero],
end

lemma epi_to_Condensed_map {A B : CompHausFiltPseuNormGrp₁.{u}}
  (f : A ⟶ B) (r : ℝ≥0) (hr : 1 ≤ r) (hf : exact_with_constant f (0 : B ⟶ B) r) :
  epi (to_Condensed.map f) :=
begin
  refine ((abelian.tfae_epi (to_Condensed.obj B) (to_Condensed.map f)).out 2 0).mp _,
  have := exact_of_exact_with_constant f (0 : B ⟶ B) r hr hf,
  simpa only [to_Condensed_map_zero]
end

end condensed
