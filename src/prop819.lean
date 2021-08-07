import algebra.homology.homological_complex
import topology.category.Profinite.cofiltered_limit

import for_mathlib.Cech.split
import for_mathlib.Profinite.arrow_limit
import for_mathlib.Profinite.clopen_limit
import for_mathlib.simplicial.complex

import locally_constant.Vhat
import prop819.completion
--import prop819.locally_constant

open_locale nnreal

noncomputable theory

open category_theory opposite
open SemiNormedGroup

universes u

-- We have a surjective morphism of profinite sets.
variables (F : arrow Profinite.{u}) (surj : function.surjective F.hom)
variables (M : SemiNormedGroup.{u})

/-- The cochain complex built out of the cosimplicial object obtained by applying
  `LocallyConstant.obj M` to the augmented Cech nerve of `F`. -/
abbreviation FL : cochain_complex SemiNormedGroup ℕ :=
  (((cosimplicial_object.augmented.whiskering _ _).obj (LocallyConstant.{u u}.obj M)).obj
  F.augmented_cech_nerve.right_op).to_cocomplex

/-- The cochain complex built out of the cosimplicial object obtained by applying
  `LCC.obj M` to the augmented Cech nerve of `F`. -/
abbreviation FLC : cochain_complex SemiNormedGroup ℕ :=
  (((cosimplicial_object.augmented.whiskering _ _).obj (LCC.{u u}.obj M)).obj
  F.augmented_cech_nerve.right_op).to_cocomplex

--def Rop : (simplicial_object.augmented Profinite)ᵒᵖ ⥤ cosimplicial_object.augmented Profiniteᵒᵖ :=
--{ obj := λ X, X.unop.right_op,
--  map := λ X Y f,
--  { left := quiver.hom.op (comma_morphism.right f.unop),
--    right := nat_trans.right_op (comma_morphism.left f.unop),
--    w' := by { ext, exact congr_arg (λ η, (nat_trans.app η (op x)).op) f.unop.w.symm, } } }

/-- A functorial version of `FL`. -/
def FL_functor : (arrow Profinite.{u})ᵒᵖ ⥤ cochain_complex SemiNormedGroup ℕ :=
simplicial_object.augmented_cech_nerve.op ⋙
simplicial_to_cosimplicial_augmented _ ⋙
(cosimplicial_object.augmented.whiskering _ _).obj (LocallyConstant.obj M) ⋙
cosimplicial_object.augmented.cocomplex

/-- The functor sending an augmented cosimplicial object `X` to
  the cochain complex associated to the composition of `X` with `LCC.obj M`. -/
@[simps obj map]
def FLC_functor' : (simplicial_object.augmented Profinite.{u})ᵒᵖ ⥤ cochain_complex SemiNormedGroup ℕ :=
simplicial_to_cosimplicial_augmented _ ⋙
  (cosimplicial_object.augmented.whiskering _ _).obj (SemiNormedGroup.LCC.{u u}.obj M) ⋙
  cosimplicial_object.augmented.cocomplex

/-- A functorial version of `FLC`. -/
def FLC_functor : (arrow Profinite.{u})ᵒᵖ ⥤ cochain_complex SemiNormedGroup ℕ :=
simplicial_object.augmented_cech_nerve.op ⋙ FLC_functor' M

-- Sanity checks
example : FL F M = (FL_functor M).obj (op F) := rfl
example : FLC F M = (FLC_functor M).obj (op F) := rfl

lemma _root_.cosimplicial_object.augmented.cocomplex_map_norm_noninc
  {C₁ C₂ : cosimplicial_object.augmented SemiNormedGroup} (f : C₁ ⟶ C₂)
  (hf1 : f.left.norm_noninc) (hf2 : ∀ n, (f.right.app n).norm_noninc) (i : ℕ) :
  ((cosimplicial_object.augmented.cocomplex.map f).f i).norm_noninc :=
begin
  cases i,
  { exact hf1 },
  { exact hf2 _ },
end

lemma FLC_functor_map_norm_noninc {f g : (arrow Profinite.{u})ᵒᵖ} (α : f ⟶ g) (i : ℕ) :
  (((FLC_functor M).map α).f i).norm_noninc :=
begin
  refine cosimplicial_object.augmented.cocomplex_map_norm_noninc _ _ _ _,
  { exact SemiNormedGroup.LCC_obj_map_norm_noninc _ _ },
  { intro n,
    exact SemiNormedGroup.LCC_obj_map_norm_noninc _ _ },
end

--⊢ cosimplicial_object.δ
--      (functor.right_op F.cech_nerve ⋙ (curry.obj (uncurry.obj LocallyConstant ⋙ Completion)).obj M)
--      k =
--    Completion.map (cosimplicial_object.δ (functor.right_op F.cech_nerve ⋙ LocallyConstant.obj M) k)

lemma FLC_iso_helper {x y : simplex_category} (f : x ⟶ y) :
  (F.cech_nerve.right_op ⋙ LCC.obj M).map f =
  Completion.map ((F.cech_nerve.right_op ⋙ LocallyConstant.obj M).map f) :=
begin
  change Completion.map _ = _,
  congr' 1,
  dsimp [uncurry],
  erw locally_constant.map_hom_id,
  change 𝟙 _ ≫ _ = _,
  rw category.id_comp,
end

/--
This is a strict (i.e. norm-preserving) isomorphism between `FLC F M` and
the cochain complex obtained by mapping `FL F M` along the `Completion` functor.
-/
def FLC_iso : strict_iso ((Completion.map_homological_complex _).obj (FL F M)) (FLC F M) :=
{ iso := homological_complex.hom.iso_of_components
    (λ i, nat.rec_on i (eq_to_iso rfl) (λ _ _, eq_to_iso rfl))
    begin
      rintro (_|i) (_|j) (_|⟨i,w⟩); ext,
      { dsimp only [],
        delta FLC FL,
        dsimp only [
          cosimplicial_object.augmented.whiskering,
          cosimplicial_object.augmented.whiskering_obj,
          cosimplicial_object.augmented.to_cocomplex,
          cosimplicial_object.augmented.to_cocomplex_obj,
          cochain_complex.of,
          functor.map_homological_complex ],
        rw dif_pos rfl,
        rw dif_pos rfl,
        erw [category.id_comp, category.comp_id, category.comp_id, category.comp_id],
        dsimp only [cosimplicial_object.augmented.to_cocomplex_d,
          cosimplicial_object.augmented.drop, comma.snd, cosimplicial_object.whiskering,
          whiskering_right, cosimplicial_object.coboundary, functor.const_comp, LCC],
        simp only [quiver.hom.unop_op, arrow.augmented_cech_nerve_hom_app,
          whisker_right_app, nat_trans.comp_app, curry.obj_obj_map, category.id_comp,
          nat_trans.right_op_app, uncurry.obj_map, nat_trans.id_app,
          simplicial_object.augmented.right_op_hom,
          category_theory.functor.map_id, category_theory.functor.comp_map,
          SemiNormedGroup.LocallyConstant_obj_map, SemiNormedGroup.Completion_map],
        erw category.id_comp },
      { dsimp only [],
        delta FLC FL,
        dsimp only [
          cosimplicial_object.augmented.whiskering,
          cosimplicial_object.augmented.whiskering_obj,
          cosimplicial_object.augmented.to_cocomplex,
          cosimplicial_object.augmented.to_cocomplex_obj,
          cochain_complex.of,
          functor.map_homological_complex ],
        rw dif_pos rfl,
        rw dif_pos rfl,
        erw [category.id_comp, category.comp_id, category.comp_id, category.comp_id],
        dsimp only [
          cosimplicial_object.augmented.to_cocomplex_d,
          cosimplicial_object.augmented.drop,
          comma.snd,
          cosimplicial_object.whiskering,
          whiskering_right,
          cosimplicial_object.coboundary,
          LCC ],
        rw [Completion.map_sum],
        congr,
        funext k,
        rw [Completion.map_gsmul],
        congr' 1,
        apply FLC_iso_helper }
    end,
  is_strict := λ i, { strict_hom' := λ a, by { cases i; refl } } }.

open_locale simplicial

-- TODO: Move this to mathlib (also relax the has_limits condition).
/-- the isomorphism between the 0-th term of the Cech nerve and F.left-/
@[simps]
def cech_iso_zero {C : Type*} [category C] (F : arrow C) [limits.has_limits C]
  : F.cech_nerve _[0] ≅ F.left :=
{ hom := limits.wide_pullback.π _ ⟨0⟩,
  inv := limits.wide_pullback.lift F.hom (λ _, 𝟙 _) (by simp),
  hom_inv_id' := begin
    apply limits.wide_pullback.hom_ext,
    { intro i,
      simp only [limits.wide_pullback.lift_π, category.id_comp, category.comp_id, category.assoc],
      congr,
      tidy },
    { simp }
  end }

lemma augmentation_zero {C : Type*} [category C] (F : arrow C) [limits.has_limits C] :
  (cech_iso_zero F).inv ≫ F.augmented_cech_nerve.hom.app _ = F.hom := by tidy

lemma locally_constant_norm_empty (X : Profinite) (hX : ¬ nonempty X)
  (g : (LocallyConstant.obj M).obj (op X)) : ∥ g ∥ = 0 :=
begin
  rw locally_constant.norm_def,
  dsimp [supr],
  suffices : set.range (λ x : ↥X, ∥ g.to_fun x ∥) = ∅,
  { erw [this, real.Sup_empty],  },
  simp only [set.range_eq_empty, not_nonempty_iff],
  exact not_nonempty_iff.mp hX
end

lemma Profinite.coe_comp_apply {X Y Z : Profinite} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
  (f ≫ g) x = g (f x) := rfl

lemma locally_constant_to_fun_eq {X : Profinite} (f : locally_constant X M) :
  f.to_fun = f := rfl

lemma locally_constant_eq {X : Profinite} (f g : locally_constant X M) :
  f.to_fun = g.to_fun ↔ f = g :=
begin
  split,
  { intro h, ext, change f.to_fun _ = _, rw h, refl, },
  { intro h, rw h }
end

lemma locally_constant_eq_zero {X : Profinite} (f : locally_constant X M) :
  f = 0 ↔ set.range f.to_fun ⊆ {0} :=
begin
  split,
  { intro h, rw h, simp, },
  { intro h, ext x,
    dsimp,
    apply h,
    use x,
    refl }
end

include surj

lemma prop819_degree_zero_helper :
  function.surjective (limits.wide_pullback.base (λ i : ulift (fin 1), F.hom)) :=
begin
  intro x,
  obtain ⟨x,rfl⟩ := surj x,
  dsimp at *,
  refine ⟨(cech_iso_zero F).inv x, _⟩,
  dsimp,
  change (limits.wide_pullback.lift F.hom _ _ ≫ limits.wide_pullback.base _) _ = _,
  simp,
end

lemma prop819_zero_norm_le (g : (LocallyConstant.obj M).obj (op F.right)) : ∥ g ∥ ≤
  ∥(LocallyConstant.obj M).map (limits.wide_pullback.base (λ i : ulift (fin 1), F.hom)).op g∥ :=
begin
  by_cases hh : nonempty F.right,
  { apply cSup_le,
    { rcases hh with ⟨x⟩,
      refine ⟨∥g.to_fun x∥, x, rfl⟩ },
    { rintros z ⟨z,rfl⟩,
      obtain ⟨z,rfl⟩ := (prop819_degree_zero_helper _ surj) z,
      change ∥g.to_fun _∥ ≤ _,
      erw ← LocallyConstant_map_apply M _ F.right (limits.wide_pullback.base (λ i, F.hom)) g z,
      apply locally_constant.norm_apply_le } },
  { rw locally_constant_norm_empty _ _ hh g,
    simp }
end

theorem prop819_degree_zero (f : (FLC F M).X 0) (hf : (FLC F M).d 0 1 f = 0) :
  f = 0 :=
begin
  apply injective_of_strict_iso _ _ (FLC_iso F M) _ _ hf,
  intros f hf,
  have := @controlled_exactness ((FL F M).X 0) (0 : SemiNormedGroup) ((FL F M).X 1) _ _ _ 0 1
    zero_lt_one 1 ((FL F M).d _ _) _ _ 1 zero_lt_one f _,
  { rcases this with ⟨g,h1,h2⟩,
    rw ← h1,
    simp },
  { intros g hg,
    refine ⟨0,_, by simp⟩,
    change (FL F M).d 0 1 g = 0 at hg,
    dsimp,
    symmetry,
    delta FL at hg,
    dsimp only [cosimplicial_object.augmented.whiskering,
      cosimplicial_object.augmented.whiskering_obj,
      cosimplicial_object.augmented.to_cocomplex,
      cochain_complex.of] at hg,
    rw dif_pos at hg,
    swap, {simp},
    dsimp [cosimplicial_object.augmented.to_cocomplex_d] at hg,
    ext x,
    obtain ⟨x,rfl⟩ := (prop819_degree_zero_helper F surj) x,
    apply_fun (λ e, e x) at hg,
    rw locally_constant.coe_comap at hg,
    swap, { continuity },
    exact hg },
  { rintro g ⟨g,rfl⟩,
    refine ⟨g,rfl,_⟩,
    dsimp [cosimplicial_object.augmented.to_cocomplex_d],
    simp only [locally_constant.comap_hom_apply, one_mul,
      if_true, eq_self_iff_true, category.id_comp, category.comp_id],
    apply prop819_zero_norm_le _ surj },
  { exact hf }
end
.

/-- Any discrete quotient `S` of `F.left` yields a cochain complex, as follows.
First, let `T` be the maximal quotient of `F.right` such that `F.hom : F.left ⟶ F.right`
descends to `S → T`. Next construct the augmented Cech nerve of `S → T`, and finally
apply `FL_functor M` to this augmented Cech nerve.
-/
def FLF : (discrete_quotient F.left)ᵒᵖ ⥤ cochain_complex SemiNormedGroup ℕ :=
(Profinite.arrow_diagram F surj).op ⋙ FL_functor M

/--
The diagram of cochain complexes given by `FLF F surj` fits together into a cocone
whose cocone point is defeq to `FL F M`. This is precisely this cocone.
-/
def FLF_cocone : limits.cocone (FLF F surj M) :=
(FL_functor M).map_cocone $ (Profinite.arrow_cone F surj).op

open Profinite

lemma exists_locally_constant_FLF (n : ℕ) (f : (FL F M).X (n+1)) :
  ∃ (S : discrete_quotient F.left) (g : ((FLF F surj M).obj (op S)).X (n+1)),
    ((FLF_cocone F surj M).ι.app (op S)).f _ g = f :=
begin
  have hC := Cech_cone_is_limit F surj n,
  obtain ⟨i,g,hg⟩ := Profinite.exists_locally_constant _ hC f,
  use [i, g],
  exact hg.symm,
end

lemma FLF_cocone_app_coe_eq (n : ℕ) (S : discrete_quotient F.left)
  (g : ((FLF F surj M).obj (op S)).X (n+1)) :
  (((FLF_cocone F surj M).ι.app (op S)).f _ g).to_fun =
    g.to_fun ∘ ((Cech_cone F surj n).π.app _) :=
begin
  ext x,
  change locally_constant.comap _ _ _ = _,
  rw locally_constant.coe_comap,
  swap, { continuity },
  refl,
end

lemma FLF_map_coe_eq (n : ℕ) (S T : discrete_quotient F.left) (hh : T ≤ S)
  (g : ((FLF F surj M).obj (op S)).X (n+1)) :
  (((FLF F surj M).map (hom_of_le hh).op).f _ g).to_fun  =
  g.to_fun ∘ ((Cech_cone_diagram F surj n).map (hom_of_le hh)) :=
begin
  ext x,
  change locally_constant.comap _ _ _ = _,
  rw locally_constant.coe_comap,
  swap, { continuity },
  refl,
end

lemma eq_zero_FLF (n : ℕ) (S : discrete_quotient F.left)
  (g : ((FLF F surj M).obj (op S)).X (n+1))
  (hg : ((FLF_cocone F surj M).ι.app (op S)).f _ g = 0) :
  ∃ (T : discrete_quotient F.left) (hT : T ≤ S),
    ((FLF F surj M).map (hom_of_le hT).op).f _ g = 0 :=
begin
  have := exists_image (Cech_cone_diagram F surj n)
    (Cech_cone F surj n) (Cech_cone_is_limit F surj n) S,
  obtain ⟨T,hT,hh⟩ := this,
  use T, use hT,
  rw [locally_constant_eq_zero, FLF_map_coe_eq],
  rw [locally_constant_eq_zero, FLF_cocone_app_coe_eq]  at hg,
  rintro x ⟨x,rfl⟩,
  apply hg,
  let P : (Cech_cone F surj n).X ⟶ (Cech_cone_diagram F surj n).obj S :=
    (Cech_cone F surj n).π.app _,
  let p : (Cech_cone_diagram F surj n).obj T ⟶ (Cech_cone_diagram F surj n).obj S :=
    (Cech_cone_diagram F surj n).map (hom_of_le hT),
  change ↥((Cech_cone_diagram F surj n).obj T) at x,
  have : p x ∈ set.range p, use x,
  erw ← hh at this,
  obtain ⟨y,hy⟩ := this,
  dsimp only [p] at hy,
  use y,
  dsimp only [function.comp_apply],
  erw hy,
end
.

lemma d_eq_zero_FLF (n : ℕ) (S : discrete_quotient F.left)
  (g : ((FLF F surj M).obj (op S)).X (n+1))
  (hg : (FL F M).d (n+1) (n+2)
    (((FLF_cocone F surj M).ι.app (op S)).f _ g) = 0) :
  ∃ (T : discrete_quotient F.left) (hT : T ≤ S),
  ((FLF F surj M).obj (op T)).d (n+1) (n+2)
    (((FLF F surj M).map $ (hom_of_le hT).op).f _ g) = 0 :=
begin
  have := ((FLF_cocone F surj M).ι.app (op S)).comm (n+1) (n+2),
  apply_fun (λ e, e g) at this,
  erw this at hg,
  dsimp only [SemiNormedGroup.coe_comp] at hg,
  have := eq_zero_FLF F surj M (n+1) S _ hg,
  obtain ⟨T,hT,h⟩ := this,
  use T, use hT,
  have hh := ((FLF F surj M).map (hom_of_le hT).op).comm (n+1) (n+2),
  apply_fun (λ e, e g) at hh,
  erw ← hh at h,
  exact h,
end

lemma norm_eq_FLF (n : ℕ) (S : discrete_quotient F.left)
  (g : ((FLF F surj M).obj (op S)).X (n+1)) :
  ∃ (T : discrete_quotient F.left) (hT : T ≤ S),
    ∥((FLF_cocone F surj M).ι.app (op S)).f _ g∥₊ =
    ∥(((FLF F surj M)).map (hom_of_le hT).op).f _ g∥₊ :=
begin
  have := exists_image (Cech_cone_diagram F surj n)
    (Cech_cone F surj n) (Cech_cone_is_limit F surj n) S,
  obtain ⟨T,hT,hh⟩ := this,
  use T, use hT,
  ext,
  dsimp,
  change Sup _ = Sup _,
  congr' 1,
  ext r,
  split,
  { rintros ⟨x,rfl⟩,
    dsimp only,
    change ↥(Cech_cone F surj n).X at x,
    use (Cech_cone F surj n).π.app T x,
    dsimp only,
    rw [← locally_constant_to_fun_eq, FLF_map_coe_eq,
      function.comp_apply, ← Profinite.coe_comp_apply,
      (Cech_cone F surj n).w, ← locally_constant_to_fun_eq,
      FLF_cocone_app_coe_eq],
    refl },
  { rintros ⟨x,rfl⟩,
    dsimp only,
    change ↥((Cech_cone_diagram F surj n).obj T) at x,
    have : (Cech_cone_diagram F surj n).map (hom_of_le hT) x ∈
      set.range ((Cech_cone_diagram F surj n).map (hom_of_le hT)), use x,
    rw ← hh at this,
    obtain ⟨y,hy⟩ := this,
    change ↥(Cech_cone F surj n).X at y,
    use y,
    dsimp only,
    simp_rw ← locally_constant_to_fun_eq,
    rw [FLF_map_coe_eq, FLF_cocone_app_coe_eq],
    dsimp only [function.comp_apply],
    erw hy }
end

lemma exists_locally_constant (n : ℕ) (f : (FL F M).X (n+1))
  (hf : (FL F M).d _ (n+2) f = 0) :
  -- TODO: ∃ ..., true looks a bit fuuny
  ∃ (S : discrete_quotient F.left)
    (g : ((FLF F surj M).obj (op S)).X (n+1))
    (hgf : ((FLF_cocone F surj M).ι.app (op S)).f _ g = f)
    (hgd : (((FLF F surj M).obj (op S)).d _ (n+2) g = 0))
    (hgnorm : ∥f∥₊ = ∥g∥₊), true :=
begin
  obtain ⟨S,f,rfl⟩ := exists_locally_constant_FLF F surj M n f,
  obtain ⟨T1,hT1,h1⟩ := d_eq_zero_FLF F surj M n S f hf,
  obtain ⟨T2,hT2,h2⟩ := norm_eq_FLF F surj M n S f,
  let T := T1 ⊓ T2,
  have hT : T ≤ S := le_trans inf_le_left hT1,
  have hhT1 : T ≤ T1 := inf_le_left,
  have hhT2 : T ≤ T2 := inf_le_right,
  let g := ((FLF F surj M).map (hom_of_le hT).op).f _ f,
  let g1 := ((FLF F surj M).map (hom_of_le hT1).op).f _ f,
  let g2 := ((FLF F surj M).map (hom_of_le hT2).op).f _ f,
  have hg1 : ((FLF F surj M).map (hom_of_le hhT1).op).f _ g1 = g,
  { dsimp only [g, g1],
    have : (hom_of_le hT).op = (hom_of_le hT1).op ≫ (hom_of_le hhT1).op, refl,
    rw [this, functor.map_comp],
    refl },
  have hg2 : ((FLF F surj M).map (hom_of_le hhT2).op).f _ g2 = g,
  { dsimp only [g, g2],
    have : (hom_of_le hT).op = (hom_of_le hT2).op ≫ (hom_of_le hhT2).op, refl,
    rw [this, functor.map_comp],
    refl },
  refine ⟨T, g, _, _, _, trivial⟩,
  { rw ← (FLF_cocone F surj M).w (hom_of_le hT).op,
    refl },
  { rw ← hg1,
    have := ((FLF F surj M).map (hom_of_le hhT1).op).comm (n+1) (n+2),
    apply_fun (λ e, e g1) at this,
    erw this, clear this,
    dsimp only [g1, SemiNormedGroup.coe_comp, function.comp_app],
    rw [h1, normed_group_hom.map_zero] },
  { apply le_antisymm,
    { dsimp only [g],
      have := (FLF_cocone F surj M).w (hom_of_le hT).op,
      rw ← this, clear this,
      apply LocallyConstant_obj_map_norm_noninc },
    { rw [← hg2, h2],
      apply LocallyConstant_obj_map_norm_noninc } }
end

lemma FLF_norm_noninc (n : ℕ) (S : discrete_quotient F.left)
  (f : ((FLF F surj M).obj (op S)).X n) :
  ∥((FLF_cocone F surj M).ι.app (op S)).f _ f∥₊ ≤ ∥f∥₊ :=
begin
  cases n,
  apply LocallyConstant_obj_map_norm_noninc,
  apply LocallyConstant_obj_map_norm_noninc,
end

theorem prop819 {m : ℕ} (ε : ℝ≥0) (hε : 0 < ε)
  (f : (FLC F M).X (m+1)) (hf : (FLC F M).d (m+1) (m+2) f = 0) :
  ∃ g : (FLC F M).X m, (FLC F M).d m (m+1) g = f ∧ ∥g∥₊ ≤ (1 + ε) * ∥f∥₊ :=
begin
  apply exact_of_strict_iso _ _ (FLC_iso F M) ε hε _ _ _ hf,
  apply cmpl_exact_of_exact _ _ hε,
  clear hf f m hε ε,
  intros n f hf,
  -- We've reduced to the non-completed case.
  have := exists_locally_constant F surj M _ f hf,
  rcases this with ⟨S,g,rfl,h2,h3,-⟩,
  --let gg := ((FLF_cocone F surj M).ι.app (op S)).f _ g,
  let CC : Π (n : ℕ), ((FLF F surj M).obj (op S)).X (n+1) ⟶
      ((FLF F surj M).obj (op S)).X n :=
      ((Profinite.arrow_diagram F surj).obj S).contracting_homotopy
      (LocallyConstant.{u u}.obj M),
  let gc := CC _ g,
  let GG := ((FLF_cocone F surj M).ι.app (op S)).f _ gc,
  refine ⟨GG,_,_⟩,
  { dsimp only [GG],
    have := ((FLF_cocone F surj M).ι.app (op S)).comm n (n+1),
    apply_fun (λ e, e gc) at this,
    erw this, clear this,
    change ((FLF_cocone F surj M).ι.app (op S)).f (n + 1) _ = _,
    congr' 1,
    change (CC n ≫ _) g = g,
    cases n,
    { have hh := arrow.is_contracting_homotopy_one (LocallyConstant.{u u}.obj M)
        ((Profinite.arrow_diagram F surj).obj S),
      apply_fun (λ e, e g) at hh,
      change CC 1 (_) + _ = g at hh,
      conv at hh {
        congr,
        congr,
        erw h2 },
      rw [normed_group_hom.map_zero, zero_add] at hh,
      exact hh },
    { have hh := arrow.is_contracting_homotopy (LocallyConstant.{u u}.obj M)
        ((Profinite.arrow_diagram F surj).obj S) _,
      apply_fun (λ e, e g) at hh,
      change CC _ (_) + _ = g at hh,
      conv at hh {
        congr,
        congr,
        erw h2 },
      rw [normed_group_hom.map_zero, zero_add] at hh,
      exact hh } },
  { rw h3,
    suffices : ∥GG∥₊ ≤ ∥gc∥₊,
    { apply le_trans this _,
      cases n,
      apply LocallyConstant_obj_map_norm_noninc,
      apply LocallyConstant_obj_map_norm_noninc },
    apply FLF_norm_noninc }
end
