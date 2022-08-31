import breen_deligne.main
import breen_deligne.eg
import condensed.tensor_short_exact
import condensed.evaluation_homology
import condensed.sheafification_homology
import pseudo_normed_group.QprimeFP
import for_mathlib.AddCommGroup
import for_mathlib.map_to_sheaf_is_iso
import condensed.is_iso_iff_extrdisc
import Lbar.torsion_free_condensed
import condensed.ab5
import condensed.ab4
import for_mathlib.endomorphisms.ab4
import for_mathlib.homology_exact
import condensed.Qprime_isoms2
import for_mathlib.free_abelian_exact
import for_mathlib.unflip
import breen_deligne.eval_Pow_functor_nat_trans_compatibility

.

noncomputable theory

universes u

open category_theory category_theory.limits breen_deligne opposite
open_locale big_operators

section
open category_theory.preadditive

attribute [simps map] AddCommGroup.free

lemma oof (A B : AddCommGroup.{u}) : (A →+ B) = (A ⟶ B) := rfl

lemma reorder {M : Type*} [add_comm_monoid M] (a b c d : M) :
  (a + b) + (c + d) = (a + c) + (b + d) :=
by { simp only [add_assoc, add_left_comm b c d], }

def eval_free_π (A : AddCommGroup.{u}) (i : fin 2) : (preadditive.Pow 2).obj A ⟶ (preadditive.Pow 1).obj A :=
biproduct.π _ i ≫ biproduct.ι (λ _, A) 0

lemma eval_free_π_eq (A : AddCommGroup.{u}) (k : fin 2) :
  eval_free_π A k = biproduct.matrix
    (λ (i : (fin 2)) (j : (fin 1)), basic_universal_map.proj 1 k j i • 𝟙 A) :=
begin
  apply biproduct.hom_ext, rintro j, fin_cases j,
  rw [biproduct.matrix_π, eval_free_π, category.assoc, biproduct.ι_π, dif_pos rfl, eq_to_hom_refl,
    category.comp_id],
  apply biproduct.hom_ext', rintro i, rw [biproduct.ι_desc],
  suffices : basic_universal_map.proj 1 k 0 i = if i = k then 1 else 0,
  { rw [this, biproduct.ι_π], dsimp, obtain (rfl|hik) := eq_or_ne i k,
    { rw [if_pos rfl, if_pos rfl, one_smul], },
    { rw [if_neg, if_neg hik, zero_smul],
      intro H, apply hik, exact H } },
  { dsimp [basic_universal_map.proj, basic_universal_map.proj_aux], dec_trivial! },
end

def eval_free_σ (A : AddCommGroup.{u}) : (preadditive.Pow 2).obj A ⟶ (preadditive.Pow 1).obj A :=
eval_free_π A 0 + eval_free_π A 1

lemma eval_free_d10 (A : AddCommGroup.{u}) :
  (((data.eval_functor (forget _ ⋙ AddCommGroup.free)).obj breen_deligne.eg.data).obj A).d 1 0 =
  ((forget _ ⋙ AddCommGroup.free).map $ eval_free_π A 0) +
  ((forget _ ⋙ AddCommGroup.free).map $ eval_free_π A 1) -
  ((forget _ ⋙ AddCommGroup.free).map $ eval_free_σ A) :=
begin
  dsimp only [eg, eg.BD, data.eval_functor_obj_obj_d], rw [dif_pos rfl],
  dsimp only [universal_map.eval_Pow], rw [lift_app],
  dsimp only [whisker_right_app, eg.map, eg.σπ, universal_map.proj, universal_map.sum],
  simp only [add_monoid_hom.map_sub, free_abelian_group.lift.of,
    basic_universal_map.eval_Pow_app, functor.comp_map, forget_map_eq_coe, sub_comp, add_comp,
    preadditive.Pow_obj, forget_obj_eq_coe, fin.sum_univ_two, add_monoid_hom.map_add],
  refine congr_arg2 _ (congr_arg2 _ _ _) _; congr' 2,
  { rw eval_free_π_eq, refl, },
  { rw eval_free_π_eq, refl, },
  { rw [eval_free_σ, eval_free_π_eq, eval_free_π_eq],
    apply biproduct.hom_ext, rintro j, fin_cases j, simp only [add_comp, biproduct.matrix_π],
    erw [biproduct.matrix_π, biproduct.matrix_π],
    apply biproduct.hom_ext', rintro i, simp only [comp_add, biproduct.ι_desc, ← add_smul],
    refl }
end

def Pow_1_iso (A : AddCommGroup.{u}) : (preadditive.Pow 1).obj A ≅ A :=
{ hom := biproduct.π (λ _, A) 0,
  inv := biproduct.ι (λ _, A) 0,
  hom_inv_id' := begin
    erw [← biproduct.total, fin.sum_univ_one],
  end,
  inv_hom_id' := by simp only [biproduct.ι_π, dif_pos rfl, eq_to_hom_refl] }

def Pow_2_iso (A : AddCommGroup.{u}) : (preadditive.Pow 2).obj A ≅ AddCommGroup.of (A × A) :=
{ hom := add_monoid_hom.prod (biproduct.π (λ _, A) 0) (biproduct.π (λ _, A) 1),
  inv := add_monoid_hom.coprod (biproduct.ι (λ _, A) 0) (biproduct.ι (λ _, A) 1),
  hom_inv_id' := begin
    ext x, erw [← biproduct.total, comp_apply],
    --swap, apply_instance,
    dsimp only [add_monoid_hom.coprod_apply, add_monoid_hom.prod_apply],
    simp only [← comp_apply, fin.sum_univ_two], refl,
  end,
  inv_hom_id' := begin
    ext1 x, rw [comp_apply, id_apply],
    dsimp only [add_monoid_hom.coprod_apply, add_monoid_hom.prod_apply],
    simp only [add_monoid_hom.map_add, ← comp_apply, biproduct.ι_π, dif_pos rfl, eq_to_hom_refl, id_apply],
    rw [dif_neg], swap, dec_trivial,
    rw [dif_neg], swap, dec_trivial,
    erw [add_zero, zero_add], cases x, refl,
  end }
.

lemma eval_free_π_eq_fst (A : AddCommGroup.{u}) :
  (Pow_2_iso A).inv ≫ eval_free_π A 0 ≫ (Pow_1_iso A).hom =
  AddCommGroup.of_hom (add_monoid_hom.fst A A) :=
begin
  ext x, simp only [comp_apply],
  dsimp only [Pow_2_iso, Pow_1_iso, eval_free_π, add_monoid_hom.coprod_apply],
  simp only [← comp_apply, category.assoc, biproduct.ι_π, dif_pos rfl, eq_to_hom_refl,
    category.comp_id, add_monoid_hom.map_add, id_apply],
  erw [dif_neg, add_zero], refl, dec_trivial,
end

lemma eval_free_π_eq_snd (A : AddCommGroup.{u}) :
  (Pow_2_iso A).inv ≫ eval_free_π A 1 ≫ (Pow_1_iso A).hom =
  AddCommGroup.of_hom (add_monoid_hom.snd A A) :=
begin
  ext x, simp only [comp_apply],
  dsimp only [Pow_2_iso, Pow_1_iso, eval_free_π, add_monoid_hom.coprod_apply],
  simp only [← comp_apply, category.assoc, biproduct.ι_π, dif_pos rfl, eq_to_hom_refl,
    category.comp_id, add_monoid_hom.map_add, id_apply],
  erw [dif_neg, zero_add], refl, dec_trivial,
end

lemma eval_free_σ_eq_add (A : AddCommGroup.{u}) :
  (Pow_2_iso A).inv ≫ eval_free_σ A ≫ (Pow_1_iso A).hom =
  AddCommGroup.of_hom (add_monoid_hom.coprod (add_monoid_hom.id _) (add_monoid_hom.id _)) :=
by { simp only [eval_free_σ, add_comp, comp_add, eval_free_π_eq_fst, eval_free_π_eq_snd], refl, }

lemma eval_free_homology_zero_exact (A : AddCommGroup.{u}) :
  exact
  ((((data.eval_functor (forget _ ⋙ AddCommGroup.free)).obj breen_deligne.eg.data).obj A).d 1 0)
  ((forget _ ⋙ AddCommGroup.free).map (Pow_1_iso A).hom ≫ AddCommGroup.of_hom (free_abelian_group.lift id)) :=
begin
  let F := forget _ ⋙ AddCommGroup.free,
  refine exact_of_iso_of_exact' _ _ _ _
    (F.map_iso (Pow_2_iso A).symm) (F.map_iso (Pow_1_iso A).symm) (iso.refl _) _ _
    (free_abelian_group.exact_σπ A),
  swap,
  { dsimp only [functor.map_iso_hom, iso.symm_hom, iso.refl_hom, F],
    rw [category.comp_id, ← functor.map_iso_inv, ← functor.map_iso_hom, iso.inv_hom_id_assoc], },
  rw [← iso.comp_inv_eq, category.assoc, eval_free_d10],
  simp only [comp_add, add_comp, comp_sub, sub_comp],
  refine congr_arg2 _ (congr_arg2 _ _ _) _,
  { simp only [functor.map_iso_hom, functor.map_iso_inv, iso.symm_hom, iso.symm_inv,
      ← functor.map_comp, eval_free_π_eq_fst], refl },
  { simp only [functor.map_iso_hom, functor.map_iso_inv, iso.symm_hom, iso.symm_inv,
      ← functor.map_comp, eval_free_π_eq_snd], refl },
  { simp only [functor.map_iso_hom, functor.map_iso_inv, iso.symm_hom, iso.symm_inv,
      ← functor.map_comp, eval_free_σ_eq_add], refl },
end

instance eval_free_homology_zero_epi (A : AddCommGroup.{u}) :
  epi ((forget _ ⋙ AddCommGroup.free).map (Pow_1_iso A).hom ≫ AddCommGroup.of_hom (free_abelian_group.lift id)) :=
begin
  apply_with epi_comp {instances:=ff}, apply_instance,
  rw [AddCommGroup.epi_iff_surjective], intro a,
  exact ⟨free_abelian_group.of a, free_abelian_group.lift.of _ _⟩
end

open_locale zero_object

section

variables {𝓐 : Type*} [category 𝓐] [abelian 𝓐]
variables {A B C X : 𝓐} (f : A ⟶ B) (g : B ⟶ C) (γ : B ⟶ X)

def of_epi_g (hfg : exact f g) (hg : epi g) (hγ : γ = 0) :
  homology_iso_datum f γ C :=
{ w := by rw [hγ, comp_zero],
  K := B,
  ι := 𝟙 B,
  f' := f,
  fac' := category.comp_id _,
  zero₁' := by rw [hγ, comp_zero],
  π := g,
  zero₂' := hfg.w,
  fork_is_limit := is_limit_aux _ (λ s, s.ι) (λ s, by apply category.comp_id)
      (λ s m hm, begin rw [← hm], symmetry, apply category.comp_id, end),
  cofork_is_colimit := @abelian.is_colimit_of_exact_of_epi _ _ _ _ _ _ _ _ hg hfg }

@[simp] lemma of_epi_g.to_homology_iso_predatum_π
  (hfg : exact f g) (hg : epi g) (hγ : γ = 0) :
  (of_epi_g f g γ hfg hg hγ).to_homology_iso_predatum.π = g := rfl

end

def nat_trans_eval_free :
  ((data.eval_functor (forget _ ⋙ AddCommGroup.free.{u})).obj breen_deligne.eg.data) ⋙
    homological_complex.eval _ _ 0 ⟶ 𝟭 AddCommGroup :=
{ app := λ A, (forget _ ⋙ AddCommGroup.free).map (Pow_1_iso A).hom ≫
    AddCommGroup.of_hom (free_abelian_group.lift id),
  naturality' := λ A₁ A₂ f, begin
    simp only [functor.comp_map, homological_complex.eval_map, data.eval_functor_obj_map_f,
      forget_map_eq_coe, AddCommGroup.free_map, functor.id_map, category.assoc],
    ext x,
    dsimp [eg, eg.BD, eg.rank] at x,
    have h : ∃ y, x = (Pow_1_iso A₁).inv y,
    { use (Pow_1_iso A₁).hom x,
      rw [← comp_apply, iso.hom_inv_id, id_apply], },
    cases h with y hy,
    subst hy,
    simp only [comp_apply, free_abelian_group.map_of_apply, AddCommGroup.of_hom_apply,
      free_abelian_group.lift.of, id.def, iso.inv_hom_id_apply, biproduct.map_eq],
    let z : fin (eg.data.X 0) := ⟨0, begin
      dsimp [eg, eg.BD, eg.rank],
      linarith,
    end⟩,
    rw finset.sum_eq_single z, rotate,
    { intros b hb₁ hb₂,
      exfalso,
      apply hb₂,
      --cases b,
      --simp only [ulift.up_inj],
      rw fin.eq_mk_iff_coe_eq,
      have hb₃ := b.is_lt,
      dsimp [eg, eg.BD, eg.rank] at hb₃,
      linarith, },
    { intro h,
      exfalso,
      apply h,
      simp only [finset.mem_univ], },
    simp only [← comp_apply, category.assoc],
    congr' 1,
    dsimp,
    change _ ≫ (Pow_1_iso A₁).hom ≫ _ ≫ (Pow_1_iso A₂).inv ≫ _ = _,
    rw [iso.inv_hom_id, iso.inv_hom_id_assoc, category.comp_id],
  end, }

def short_complex_nat_trans_eval_free :
  ((data.eval_functor (forget _ ⋙ AddCommGroup.free)).obj breen_deligne.eg.data)
    ⋙ short_complex.functor_homological_complex _ _ 0 ⟶ short_complex.ι_middle :=
begin
  refine short_complex.nat_trans_hom_mk 0 nat_trans_eval_free 0 _
    (begin apply is_zero.eq_of_tgt, apply short_complex.ι_middle_π₃_is_zero, end),
  ext1, ext1 A,
  simp only [zero_comp, nat_trans.app_zero, nat_trans.hcomp_app, nat_trans.comp_app,
    nat_trans.id_app, short_complex.π₂.map_id, category.comp_id],
  dsimp only [short_complex.φ₁₂, short_complex.functor_homological_complex, functor.comp_obj,
    short_complex.mk],
  simp only [@homological_complex.d_to_eq _ _ _ _ (complex_shape.down ℕ) _ 1 0 (zero_add 1),
    category.assoc],
  erw [(eval_free_homology_zero_exact A).w, comp_zero],
end

lemma short_complex_nat_trans_eval_free_app_τ₂ (A : AddCommGroup) :
  (short_complex_nat_trans_eval_free.app A).τ₂ = nat_trans_eval_free.app A := rfl

def eval_free_homology_zero_nat_trans :=
short_complex_nat_trans_eval_free ◫ (𝟙 short_complex.homology_functor)

lemma _root_.short_complex.homology_map_is_iso_of_exact_and_epi
  {A : Type*} [category A] [abelian A]
  {S₁ S₂ : short_complex A} (φ : S₁ ⟶ S₂) (hg₁ : S₁.1.g = 0) (hf₂ : S₂.1.f = 0) (hg₂ : S₂.1.g = 0)
  (ex : exact S₁.1.f φ.τ₂) (epi_τ₂ : epi φ.τ₂) :
  is_iso (short_complex.homology_functor.map φ) :=
begin
  let h₁ := homology_iso_datum.of_g_is_zero S₁.1.f S₁.1.g hg₁,
  let h₂ := homology_iso_datum.of_both_zeros S₂.1.f S₂.1.g hf₂ hg₂,
  let ψ := cokernel.desc _ φ.τ₂ ex.w,
  let μ : homology_map_datum φ h₁ h₂ ψ :=
  { κ := φ.τ₂,
    fac₁' := by { erw [φ.comm₁₂], simp only [hf₂], refl, },
    fac₂' := by { erw [category.id_comp, category.comp_id], },
    fac₃' := by { erw [category.comp_id], apply cokernel.π_desc, }, },
  rw μ.homology_map_eq,
  suffices : is_iso ψ,
  { haveI := this, apply_instance, },
  exact abelian.category_theory.limits.cokernel.desc.category_theory.is_iso _ _ ex,
end

instance : is_iso eval_free_homology_zero_nat_trans.{u} :=
begin
  suffices : ∀ A, is_iso ((short_complex_nat_trans_eval_free ◫
    (𝟙 short_complex.homology_functor)).app A),
  { apply_with nat_iso.is_iso_of_is_iso_app { instances := ff }, exact this, },
  intro A,
  simp only [nat_trans.hcomp_id_app],
  refine short_complex.homology_map_is_iso_of_exact_and_epi _ _ rfl rfl _ _,
  { apply homological_complex.shape,
    simp only [chain_complex.next_nat_zero, complex_shape.down_rel,
      nat.one_ne_zero, not_false_iff], },
  { refine exact_of_iso_of_exact' _ _ _ _ _ _ _ _ _ (eval_free_homology_zero_exact A),
    { symmetry,
      exact (homological_complex.X_prev_iso _ (zero_add 1)), },
    { refl, },
    { apply eq_to_iso, cases A, refl, },
    { dsimp only [short_complex.functor_homological_complex, functor.comp_obj,
        short_complex.mk],
      rw homological_complex.d_to_eq, swap 3, exact 1, swap, dsimp, refl,
      simp only [iso.symm_hom, iso.refl_hom, category.comp_id],
      apply iso.inv_hom_id_assoc, },
    { apply category.id_comp, }, },
  { rw short_complex_nat_trans_eval_free_app_τ₂,
    dsimp [nat_trans_eval_free],
    convert eval_free_homology_zero_epi.{u} A,
    cases A,
    refl, },
end

def eval_free_homology_zero :
  ((data.eval_functor (forget _ ⋙ AddCommGroup.free)).obj breen_deligne.eg.data) ⋙
    homology_functor _ _ 0 ≅ 𝟭 _ :=
  iso_whisker_left _ (short_complex.homology_functor_iso _ _ _) ≪≫
    (functor.associator _ _ _).symm ≪≫ as_iso eval_free_homology_zero_nat_trans ≪≫
    short_complex.ι_middle_homology_nat_iso.symm

end

open bounded_homotopy_category

namespace Condensed

def HQ'Z (n : ℤ) : Ab :=
((eg.eval $ category_theory.forget AddCommGroup ⋙ AddCommGroup.free).obj
  (AddCommGroup.free.obj punit)).val.as.homology n

variables (BD : package)

-- `by apply_instance` takes for ever, so we provide this shortcut
instance : abelian (endomorphisms $ Condensed.{u} Ab.{u+1}) :=
endomorphisms.category_theory.abelian

-- `by apply_instance` takes for ever, so we provide this shortcut
instance : has_finite_biproducts (endomorphisms $ Condensed.{u} Ab.{u+1}) :=
abelian.has_finite_biproducts

-- `by apply_instance` takes for ever, so we provide this shortcut
instance : enough_projectives (endomorphisms $ Condensed.{u} Ab.{u+1}) :=
endomorphisms.category_theory.enough_projectives

-- `by apply_instance` takes for ever, so we provide this shortcut
instance : has_coproducts_of_shape (ulift.{u+1} ℕ) (endomorphisms $ Condensed.{u} Ab.{u+1}) :=
endomorphisms.has_colimits_of_shape

-- `by apply_instance` takes for ever, so we provide this shortcut
instance : has_products_of_shape (ulift.{u+1} ℕ) (endomorphisms $ Condensed.{u} Ab.{u+1}) :=
endomorphisms.has_limits_of_shape

-- `by apply_instance` takes for ever, so we provide this shortcut
instance : has_coproducts (endomorphisms $ Condensed.{u} Ab.{u+1}) :=
λ (J : Type (u+1)), endomorphisms.has_colimits_of_shape

-- `by apply_instance` takes for ever, so we provide this shortcut
instance : AB4 (endomorphisms $ Condensed.{u} Ab.{u+1}) :=
endomorphisms.category_theory.AB4 _

-- `by apply_instance` takes for ever, so we provide this shortcut
instance : has_finite_limits (endomorphisms $ Condensed.{u} Ab.{u+1}) :=
abelian.has_finite_limits

-- `by apply_instance` takes for ever, so we provide this shortcut
instance : has_finite_colimits (endomorphisms $ Condensed.{u} Ab.{u+1}) :=
abelian.has_finite_colimits
.

-- move this
attribute [reassoc] homology_bd_eval_natural

def exists_tensor_iso (A : endomorphisms (Condensed.{u} Ab.{u+1}))
  [∀ S : ExtrDisc.{u}, no_zero_smul_divisors ℤ (A.X.val.obj (op S.val))]
  (n : ℕ) :
  ((package.endo_T tensor_functor).obj A).obj (HQ'Z (-n)) ≅
      ((eg.eval freeCond'.map_endomorphisms).obj A).val.as.homology (-n) :=
begin
  refine endomorphisms.mk_iso _ _,
  { refine _ ≪≫ ((package.hH_endo₁ eg freeCond' n).app A).symm,
    refine (homology_bd_eval eg A.X (-n)).symm ≪≫ _,
    exact (package.eval'_homology eg freeCond' n).app A.X, },
  { dsimp only [iso.trans_hom, iso.symm_hom, package.endo_T_obj_obj_e, tensor_functor, HQ'Z],
    simp only [category.assoc, ← homology_bd_eval_natural_assoc],
    refine congr_arg2 _ rfl _,
    dsimp only [iso.app_hom, iso.app_inv],
    rw [← functor.comp_map, nat_trans.naturality_assoc],
    refine congr_arg2 _ rfl _,
    dsimp only [← iso.app_inv],
    rw [iso.comp_inv_eq, category.assoc, iso.eq_inv_comp],
    exact (eg.hH_endo₁_natural freeCond' A n).symm, }
end
.

-- move this
lemma is_tensor_unit_of_iso (A B : Ab) (e : A ≅ B) (ha : AddCommGroup.is_tensor_unit A) :
  AddCommGroup.is_tensor_unit B :=
begin
  obtain ⟨a, ha⟩ := ha,
  refine ⟨e.hom a, _⟩,
  intro C, specialize ha C,
  let φ := iso.AddCommGroup_iso_to_add_equiv ((preadditive_yoneda.obj C).map_iso e.op),
  exact ha.comp φ.bijective,
end

lemma bd_lemma (A : Condensed.{u} Ab.{u+1}) (B : Condensed.{u} Ab.{u+1})
  [∀ S : ExtrDisc.{u}, no_zero_smul_divisors ℤ (A.val.obj (op S.val))]
  (f : A ⟶ A) (g : B ⟶ B) :
  (∀ i, is_iso $ ((Ext' i).map f.op).app B - ((Ext' i).obj (op A)).map g) ↔
  (∀ i, is_iso $
    ((Ext i).map ((breen_deligne.eg.eval freeCond').map f).op).app ((single _ 0).obj B) -
    ((Ext i).obj (op $ (breen_deligne.eg.eval freeCond').obj A)).map ((single _ 0).map g)) :=
begin
  apply eg.main_lemma_general' _ A B f g tensor_functor tensor_punit (λ n, HQ'Z (-n)),
  { apply tensor_tunit,
    apply is_tensor_unit_of_iso
      (AddCommGroup.free.obj punit) (HQ'Z 0),
    { let e := (eval_free_homology_zero.app (AddCommGroup.free.obj punit)).symm,
      refine e ≪≫ _, clear e,
      let e := (package.eval'_homology eg (forget AddCommGroup ⋙ AddCommGroup.free) 0).symm,
      exact e.app (AddCommGroup.free.obj punit), },
    { refine ⟨free_abelian_group.of punit.star, _⟩,
      intro B, split,
      { intros f g h, ext ⟨⟩, exact h },
      { intros b, refine ⟨free_abelian_group.lift (λ _, b), _⟩,
        apply free_abelian_group.lift.of } } },
  { apply exists_tensor_iso }
end

end Condensed
