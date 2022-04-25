import free_pfpng.basic
import condensed.projective_resolution
import condensed.condensify
import condensed.adjunctions
import condensed.sheafification_mono
import condensed.coproducts
import free_pfpng.lemmas
import condensed.exact

import for_mathlib.int

.


noncomputable theory

open_locale classical

open category_theory
open opposite

universe u

def Profinite.condensed_free_pfpng (S : Profinite.{u}) : Condensed Ab :=
CompHausFiltPseuNormGrp.to_Condensed.obj $
  CompHausFiltPseuNormGrp₁.enlarging_functor.obj
  (ProFiltPseuNormGrp₁.to_CHFPNG₁.obj S.free_pfpng)

def Profinite.to_free_pfpng_level (S : Profinite.{u}) :
  S.to_Condensed ⟶ ((ProFiltPseuNormGrp₁.level.obj 1).obj S.free_pfpng).to_Condensed :=
Profinite_to_Condensed.map $ S.to_free_pfpng

def Profinite.to_condensed_free_pfpng (S : Profinite.{u}) :
  S.to_Condensed ⟶ Condensed_Ab_to_CondensedSet.obj S.condensed_free_pfpng :=
S.to_free_pfpng_level ≫
(CompHausFiltPseuNormGrp.level_Condensed_diagram_cocone
  (CompHausFiltPseuNormGrp₁.enlarging_functor.obj
  (ProFiltPseuNormGrp₁.to_CHFPNG₁.obj S.free_pfpng))).ι.app ⟨1⟩

@[simp]
lemma Profinite.to_condensed_free_pfpng_app (S T : Profinite.{u}) (f) :
  S.to_condensed_free_pfpng.val.app (op T) f = ulift.up
  ⟨_, 1, S.to_free_pfpng ∘ (ulift.down f).1,
    S.to_free_pfpng.2.comp (ulift.down f).2, rfl⟩ :=
rfl

def profinite_to_condensed_unit :
  Profinite_to_Condensed ⟶
  Profinite.extend free_pfpng_functor ⋙
  ProFiltPseuNormGrp₁.to_CHFPNG₁ ⋙
  CompHausFiltPseuNormGrp₁.enlarging_functor ⋙
  CompHausFiltPseuNormGrp.to_Condensed ⋙
  Condensed_Ab_to_CondensedSet :=
{ app := λ S, S.to_condensed_free_pfpng,
  naturality' := λ S T f, begin
    ext X s x, induction X using opposite.rec,
    dsimp at x,
    sorry
  end }

def Profinite.free' (S : Profinite.{u}) : Condensed.{u} Ab.{u+1} :=
CondensedSet_to_Condensed_Ab'.obj S.to_Condensed

def Profinite.free'_lift (S : Profinite.{u}) {A : Condensed.{u} Ab.{u+1}}
  (η : S.to_Condensed ⟶ Condensed_Ab_to_CondensedSet.obj A) :
  S.free' ⟶ A :=
(Condensed_Ab_CondensedSet_adjunction'.hom_equiv _ _).symm η

def free'_lift {X : Type (u+1)} {A : Ab.{u+1}} (f : X → A) :
  AddCommGroup.free'.obj X ⟶ A :=
(AddCommGroup.adj'.hom_equiv _ _).symm f

-- TODO: Consider redefining `AddCommGroup.free'` so that this is true by rfl.
lemma free'_lift_eq_finsupp_lift {X : Type (u+1)} {A : Ab.{u+1}} (f : X → A) :
  free'_lift f = (finsupp.lift _ _ _ f).to_add_monoid_hom :=
begin
  dsimp [free'_lift],
  apply_fun AddCommGroup.adj'.hom_equiv X A,
  rw equiv.apply_symm_apply,
  dsimp [AddCommGroup.adj', adjunction.of_nat_iso_left,
    AddCommGroup.free_iso_free'],
  simp only [adjunction.hom_equiv_unit, forget_map_eq_coe],
  dsimp [AddCommGroup.adj, AddCommGroup.free],
  ext i,
  simp only [types_comp_apply, comp_apply, add_equiv.coe_to_add_monoid_hom,
    free_abelian_group.equiv_finsupp_apply,
    linear_map.to_add_monoid_hom_coe, finsupp.lift_apply],
  change _ = (free_abelian_group.to_finsupp (free_abelian_group.of i)).sum _,
  simp only [free_abelian_group.to_finsupp_of, finsupp.sum_single_index, zero_smul, one_zsmul],
end

open category_theory.grothendieck_topology

lemma Profinite.free'_lift_val_eq_sheafification_lift (S : Profinite.{u})
  {A : Condensed.{u} Ab.{u+1}}
  (η : S.to_Condensed ⟶ Condensed_Ab_to_CondensedSet.obj A)
  (T : Profinite.{u}) :
(S.free'_lift η).val.app (opposite.op T) =
  (sheafify_lift _ (((AddCommGroup.adj'.whiskering_right _).hom_equiv _ _).symm η.val)
    A.cond).app (opposite.op T) := rfl

def Profinite.free'_to_condensed_free_pfpng (S : Profinite.{u}) :
  S.free' ⟶ S.condensed_free_pfpng :=
S.free'_lift S.to_condensed_free_pfpng

instance : limits.has_limits_of_size.{u u} Ab.{u+1} :=
category_theory.limits.has_limits_of_size_shrink.{u u (u+1) (u+1)} Ab.{u+1}

/-- the limit `lim_i ℤ[S_i]`. -/
def Profinite.limit_free (S : Profinite.{u}) : Ab.{u+1} :=
limits.limit $ (S.fintype_diagram ⋙ forget Fintype ⋙
  AddCommGroup.free') ⋙ Ab.ulift.{u+1}

-- move me
lemma _root_.finsupp.map_domain_equiv_fun_on_fintype_symm
  {α β R : Type*} [fintype α] [semiring R] (f : α → β) (g : α → R) :
  finsupp.map_domain f (finsupp.equiv_fun_on_fintype.symm g) =
    finset.univ.sum (λ (x : α), finsupp.single (f x) (g x)) :=
begin
  dsimp [finsupp.map_domain],
  rw [finsupp.sum_fintype], swap, { intro, apply finsupp.single_zero },
  simp only [finsupp.equiv_fun_on_fintype_symm_apply_to_fun],
end

-- move me
lemma _root_.finsupp.map_domain_equiv_fun_on_fintype_symm_apply
  {α β R : Type*} [fintype α] [semiring R] (f : α → β) (g : α → R) (b : β)
  [decidable_pred (λ (a : α), f a = b)] :
  finsupp.map_domain f (finsupp.equiv_fun_on_fintype.symm g) b =
    (finset.filter (λ (a : α), f a = b) finset.univ).sum g :=
begin
  rw [finsupp.map_domain_equiv_fun_on_fintype_symm, finset.sum_apply'],
  classical,
  simp only [finsupp.single_apply, ← finset.sum_filter],
  congr'
end

def Profinite.condensed_free_pfpng_specialize_cone (S B : Profinite.{u}) (b : B) :
  limits.cone ((S.fintype_diagram ⋙ forget Fintype ⋙ AddCommGroup.free') ⋙ Ab.ulift.{u+1}) :=
{ X := S.condensed_free_pfpng.val.obj (op B),
  π :=
  { app := λ T, add_monoid_hom.mk'
      (λ t, ⟨finsupp.equiv_fun_on_fintype.symm (S.free_pfpng_π T (t.down.1 b))⟩)
      begin
        intros f g,
        ext x,
        simp only [ulift.add_down, subtype.val_eq_coe,
          finsupp.equiv_fun_on_fintype_symm_apply_to_fun, finsupp.coe_add, pi.add_apply],
        erw strict_comphaus_filtered_pseudo_normed_group_hom.map_add,
        refl,
      end,
    naturality' := λ T₁ T₂ f, begin
      ext g x,
      rw [← Profinite.free_pfpng_π_w _ f],
      simp only [subtype.val_eq_coe, finsupp.equiv_fun_on_fintype_symm_apply_to_fun,
        functor.const.obj_map, comp_apply, id_apply, add_monoid_hom.mk'_apply, functor.comp_map,
        forget_map_eq_coe, concrete_category.has_coe_to_fun_Type, AddCommGroup.free'_map,
        Ab.ulift_map_apply_down, finsupp.map_domain.add_monoid_hom_apply, free_pfpng.map,
        free_pfpng_functor_map, strict_comphaus_filtered_pseudo_normed_group_hom.coe_mk],
      classical,
      rw finsupp.map_domain_equiv_fun_on_fintype_symm_apply, congr',
    end } }

def Profinite.condensed_free_pfpng_specialize (S B : Profinite.{u}) (b : B) :
  S.condensed_free_pfpng.val.obj (op B) ⟶ S.limit_free :=
limits.limit.lift _ (S.condensed_free_pfpng_specialize_cone B b)

lemma finsupp.fun_ext {α γ : Type*}
  [add_comm_group γ]
  (f g : (α →₀ ℤ) → γ)
  (haddf : ∀ x y, f (x + y) = f x + f y)
  (haddg : ∀ x y, g (x + y) = g x + g y)
  (h : ∀ x : α, f (finsupp.single x 1) = g (finsupp.single x 1)) :
  f = g :=
congr_arg add_monoid_hom.to_fun $
@finsupp.add_hom_ext α ℤ γ _ _ (add_monoid_hom.mk' f haddf) (add_monoid_hom.mk' g haddg)
begin
  intros x n,
  apply int.induction_on_iff n; clear n,
  { simp only [finsupp.single_zero, map_zero], },
  { intro n,
    { simp only [finsupp.single_add, map_add],
      simp only [h, add_monoid_hom.mk'_apply, add_left_inj], }, },
end

def ProFiltPseuNormGrp₁.limit_π_coe_eq
  {r : nnreal} {J : Type u} [small_category J]
  (F : J ⥤ ProFiltPseuNormGrp₁.{u})
  (k : (ProFiltPseuNormGrp₁.level.obj r).obj (limits.limit F))
  (j) :
  limits.limit.π F j (k.1 : limits.limit F) =
  (((ProFiltPseuNormGrp₁.level.obj r).map (limits.limit.π F j)) k).1 := rfl

lemma Profinite.mono_free'_to_condensed_free_pfpng_aux
  (S B : Profinite.{u}) (b : B) (T : discrete_quotient S)
  (t : S.to_Condensed.val.obj (op B) →₀ ℤ) :
let e : S.to_Condensed.val.obj (op B) →
    S.condensed_free_pfpng.val.obj (op B) :=
    λ f, (S.to_condensed_free_pfpng.val.app (op B) f),
    ι : S.to_Condensed.val.obj (op B) → S :=
      λ f, (ulift.down f).1 b in
    ((limits.limit.π (S.fintype_diagram ⋙ forget Fintype ⋙
      AddCommGroup.free' ⋙ Ab.ulift) T)
      (S.condensed_free_pfpng_specialize B b (free'_lift e t))).down
  = t.map_domain (T.proj ∘ ι) :=
begin
  dsimp,
  revert t,
  rw ← function.funext_iff,
  dsimp,
  change ulift.down ∘ _ = _,
  apply finsupp.fun_ext,
  { intros, simp only [function.comp_app, map_add, ulift.add_down,
      eq_self_iff_true, forall_const] },
  { intros, simp only [function.comp_app, map_zero, ulift.zero_down,
      finsupp.map_domain_add] },
  { intros,
    simp only [function.comp_app, finsupp.map_domain_single,
      free'_lift_eq_finsupp_lift],
    dsimp [Profinite.condensed_free_pfpng_specialize],
    simp only [← comp_apply],
    erw limits.limit.lift_π,
    simp only [finsupp.sum_single_index, zero_smul, one_zsmul],
    ext i,
    dsimp [Profinite.condensed_free_pfpng_specialize_cone,
      finsupp.single, Profinite.free_pfpng_π, Profinite.to_free_pfpng],
    erw ProFiltPseuNormGrp₁.limit_π_coe_eq,
    simp only [← comp_apply, category.assoc],
    dsimp [Profinite.free_pfpng_level_iso,
      limits.is_limit.cone_point_unique_up_to_iso],
    simp only [← comp_apply, category.assoc],
    erw (limits.is_limit_of_preserves (ProFiltPseuNormGrp₁.level.obj 1)
      (limits.limit.is_limit (S.fintype_diagram ⋙ free_pfpng_functor))).fac,
    erw limits.limit.lift_π,
    refl },
end

lemma Profinite.specialization_eq_zero_of_eq_zero (S B : Profinite.{u}) (b : B)
  (t : S.to_Condensed.val.obj (op B) →₀ ℤ)
  (ht : free'_lift (S.to_condensed_free_pfpng.val.app (op B)) t = 0) :
  t.map_domain (λ f, (ulift.down f).1 b) = 0 :=
begin
  apply free_pfpng.discrete_quotient_separates_points' S,
  intros T,
  apply_fun (λ e, S.condensed_free_pfpng_specialize B b e) at ht,
  rw add_monoid_hom.map_zero at ht,
  apply_fun (λ e, limits.limit.π (S.fintype_diagram ⋙ forget Fintype ⋙
    AddCommGroup.free' ⋙ Ab.ulift) T e) at ht,
  rw add_monoid_hom.map_zero at ht,
  apply_fun ulift.down at ht,
  dsimp [AddCommGroup.free'],
  rw ← finsupp.map_domain_comp,
  have := S.mono_free'_to_condensed_free_pfpng_aux B b T t,
  dsimp at this, erw ← this, exact ht
end

lemma Profinite.adj'_hom_equiv_symm_eq_free'_lift (S B : Profinite.{u}) :
    (((AddCommGroup.adj'.whisker_right Profinite.{u}ᵒᵖ).hom_equiv
      S.to_Condensed.val S.condensed_free_pfpng.val).symm
      S.to_condensed_free_pfpng.val).app (op B) =
    free'_lift (S.to_condensed_free_pfpng.val.app (op B)) :=
begin
  ext u v, dsimp [free'_lift],
  simp only [adjunction.hom_equiv_counit, whiskering_right_obj_map,
    nat_trans.comp_app, whisker_right_app,
    adjunction.whisker_right_counit_app_app],
end

open_locale big_operators
lemma finsupp.map_domain_ne_zero_of_ne_zero_of_inj_on {α β γ : Type*} [add_comm_group β]
  (t : α →₀ β) (ht : t ≠ 0) (f : α → γ)
  (hinj : set.inj_on f t.support) :
  t.map_domain f ≠ 0 :=
begin
  contrapose! ht,
  have : ∀ (e : γ) (he : e ∈ (t.map_domain f).support), ∃ (q : α) (hq : q ∈ t.support), f q = e,
  { intros e he, by_contra c, push_neg at c,
    simp only [finsupp.mem_support_iff, ne.def] at he,
    apply he,
    erw finset.sum_apply',
    apply finset.sum_eq_zero,
    intros a ha,
    dsimp [finsupp.single], rw if_neg, apply c, exact ha },
  choose q hq hh using this,
  let ι : (t.map_domain f).support → t.support :=
    λ e, ⟨q e.1 e.2, hq e.1 e.2⟩,
  have hι : function.surjective ι,
  { rintros ⟨e,he⟩, use f e,
    { simp only [finsupp.mem_support_iff, ne.def],
      rw finsupp.map_domain_apply' _ _ (set.subset.refl _) hinj he,
      simpa using he },
    { ext, dsimp,
      apply hinj, apply hq, apply he, apply hh } },
  have : (t.map_domain f).support = ∅, by simpa using ht,
  suffices : t.support = ∅, by simpa using this,
  by_contra c, change _ ≠ _ at c,
  erw ← finset.nonempty_iff_ne_empty at c,
  obtain ⟨c,hc⟩ := c, obtain ⟨⟨c,hc⟩,ee⟩ := hι ⟨c,hc⟩,
  rw this at hc, simpa using hc,
end

lemma finsupp.lift_map_domain {γ α β : Type*} [add_comm_group β]
  (f : α → β) (ι : γ → α) :
  (finsupp.lift _ ℤ _ f) ∘ finsupp.map_domain ι = finsupp.lift _ ℤ _ (f ∘ ι) :=
begin
  apply finsupp.fun_ext,
  { intros x y,
    dsimp only [function.comp_apply],
    simp only [finsupp.map_domain_add],
    erw ((finsupp.lift β ℤ α) f).to_add_monoid_hom.map_add, refl },
  { intros x y,
    erw ((finsupp.lift β ℤ γ) (f ∘ ι)).to_add_monoid_hom.map_add, refl },
  { intros x, simp },
end

lemma finsupp.lift_map_domain_apply {γ α β : Type*} [add_comm_group β]
  (f : α → β) (ι : γ → α) (e : γ →₀ ℤ) :
  (finsupp.lift _ ℤ _ f).to_add_monoid_hom (e.map_domain ι) =
  finsupp.lift _ ℤ _ (f ∘ ι) e :=
begin
  rw ← finsupp.lift_map_domain, refl,
end

lemma finsupp.card_supp_map_domain_lt {α β γ : Type*} [add_comm_group γ]
  (f : α → β) (t : α →₀ γ) (u v : α)
  (huv : u ≠ v) (hu : u ∈ t.support) (hv : v ∈ t.support)
  (hf : f u = f v) : (t.map_domain f).support.card < t.support.card :=
begin
  classical,
  have key : (finsupp.map_domain f t).support ⊆ _ := finsupp.map_domain_support,
  have : (finsupp.map_domain f t).support.card ≤ (t.support.image f).card :=
    finset.card_le_of_subset key,
  refine lt_of_le_of_lt this _,
  have key' : (t.support.image f).card ≤ t.support.card := finset.card_image_le,
  apply lt_of_le_of_ne key',
  change ¬ _,
  rw finset.card_image_eq_iff_inj_on,
  dsimp [set.inj_on],
  push_neg, use [u, hu, v, hv, hf],
end

lemma Profinite.mono_free'_to_condensed_free_pfpng_induction_aux (n : ℕ) :
  ∀ (S B : Profinite.{u}) (t : S.to_Condensed.val.obj (op B) →₀ ℤ),
    t.support.card ≤ n →
    (free'_lift (S.to_condensed_free_pfpng.val.app (op B))) t = 0 →
  (∀ (b : ↥B), finsupp.map_domain (λ f : S.to_Condensed.val.obj (op B),
    (ulift.down f).1 b) t = 0) →
  (∃ (α : Type u) [_inst_1 : fintype α] (X : α → Profinite) (π : Π (a : α), X a ⟶ B)
    (surj : ∀ (b : ↥B), ∃ (a : α) (x : ↥(X a)), (π a) x = b),
    ∀ (a : α), finsupp.map_domain (S.to_Condensed.val.map (π a).op) t = 0) :=
begin
  /-
  TODO: This proof is very slow. It would be better to pull out a few
  of the `have` statements into separate lemmas to (hopefully)
  speed this up.
  -/
  induction n,
  case nat.zero
  { intros S B t ht, simp at ht, rw ht, intros h1 h2,
    use [punit, infer_instance, λ _, B, λ _, 𝟙 _],
    split, { intros b, use [punit.star, b], refl },
    { intros _, rw finsupp.map_domain_zero, } },
  case nat.succ : n hn
  { intros S B t ht1 ht2 H,
    by_cases ht1' : t.support.card = n+1, swap,
    { apply hn, exact nat.le_of_lt_succ (nat.lt_of_le_and_ne ht1 ht1'),
      assumption' },
    clear ht1,
    let F := t.support,
    let e : F → (B ⟶ S) := λ f, f.1.1,
    obtain ⟨Q,h1,h2,ee,-⟩ : ∃ (α : Type u) (hα1 : fintype α)
      (hα2 : linear_order α) (ee : α ≃ F), true,
    { refine ⟨ulift (fin (fintype.card F)), infer_instance,
        is_well_order.linear_order well_ordering_rel,
        equiv.ulift.trans (fintype.equiv_fin _).symm, trivial⟩, },
    resetI,
    let E₀ := { a : Q × Q | a.1 < a.2 },
    let X₀ : E₀ → Profinite.{u} := λ i, Profinite.equalizer (e (ee i.1.1)) (e (ee i.1.2)),
    let π₀ : Π (i : E₀), X₀ i ⟶ B := λ i, Profinite.equalizer.ι _ _,

    have surj₀ : ∀ (b : B), ∃ (e₀ : E₀) (x : X₀ e₀), π₀ _ x = b,
    { intro b, specialize H b,
      contrapose! H,
      have key : ∀ (i j : Q) (h : i < j), e (ee i) b ≠ e (ee j) b,
      { intros i j h, specialize H ⟨⟨i,j⟩, h⟩, intro c,
        specialize H, dsimp [X₀] at H, specialize H ⟨b, c⟩,
        apply H, refl },
      apply finsupp.map_domain_ne_zero_of_ne_zero_of_inj_on,
      { intro c, rw c at ht1', simpa using ht1' },
      { intros x hx y hy hxy, dsimp at hxy,
        let i : Q := ee.symm ⟨x,hx⟩,
        let j : Q := ee.symm ⟨y,hy⟩,
        rcases lt_trichotomy i j with (hhh|hhh|hhh),
        { specialize key i j hhh, contrapose hxy, convert key,
          { dsimp [i], rw ee.apply_symm_apply, refl },
          { dsimp [j], rw ee.apply_symm_apply, refl } },
        { apply_fun (λ q, (ee q).1) at hhh, dsimp [i,j] at hhh,
          simp_rw ee.apply_symm_apply at hhh, exact hhh },
        { specialize key j i hhh, contrapose hxy, convert key.symm,
          { dsimp [j], rw ee.apply_symm_apply, refl },
          { dsimp [i], rw ee.apply_symm_apply, refl } } } },

    let f₀ : Π (i : E₀), S.to_Condensed.val.obj (op B) → S.to_Condensed.val.obj (op (X₀ i)) :=
      λ i, S.to_Condensed.val.map (π₀ i).op,

    let t₀ : Π (i : E₀), S.to_Condensed.val.obj (op (X₀ i)) →₀ ℤ :=
      λ i, t.map_domain (f₀ i),

    have card₀ : ∀ (i : E₀), (t₀ i).support.card ≤ n,
    { intros i, suffices : (t₀ i).support.card < n + 1,
        by exact nat.lt_succ_iff.mp this,
      rw ← ht1',
      fapply finsupp.card_supp_map_domain_lt,
      refine (ee i.1.1).1,
      refine (ee i.1.2).1,
      { change ¬ _,
        erw ← subtype.ext_iff,
        apply ee.injective.ne,
        apply ne_of_lt,
        exact i.2 },
      refine (ee i.1.1).2,
      refine (ee i.1.2).2,
      { dsimp [f₀, π₀, Profinite.to_Condensed], ext1, dsimp,
        -- missing Profinite.equalizer.condition
        ext t, exact t.2 } },

    have lift₀ : ∀ (i : E₀), free'_lift (S.to_condensed_free_pfpng.val.app (op (X₀ i))) (t₀ i) = 0,
    { intros i, rw free'_lift_eq_finsupp_lift, dsimp only [t₀, f₀],
      apply_fun (λ q, S.condensed_free_pfpng.val.map (π₀ i).op q) at ht2,
      rw [add_monoid_hom.map_zero, free'_lift_eq_finsupp_lift] at ht2,
      convert ht2,
      rw finsupp.lift_map_domain_apply,
      dsimp [finsupp.lift],
      rw (S.condensed_free_pfpng.val.map (π₀ i).op).map_finsupp_sum,
      refl },

    have map₀ : ∀ (i : E₀) (b : ↥(X₀ i)),
        finsupp.map_domain
          (λ (f : S.to_Condensed.val.obj (op (X₀ i))), f.down.to_fun b) (t₀ i) = 0,
    { intros i b, dsimp [t₀], rw ← finsupp.map_domain_comp,
      exact H (π₀ i b) },

    have key := λ i, hn S (X₀ i) (t₀ i) (card₀ i) (lift₀ i) (map₀ i),

    choose A hA X₁ π₁ surj₁ key using key, resetI,

    let E := Σ (e : E₀), A e,
    let X : E → Profinite.{u} := λ i, X₁ i.1 i.2,
    let π : Π (e : E), X e ⟶ B := λ e, π₁ e.1 e.2 ≫ π₀ e.1,

    use [E, infer_instance, X, π], split,

    { intros b,
      obtain ⟨e₀,x,hx⟩ := surj₀ b,
      obtain ⟨i,q,hq⟩ := surj₁ e₀ x,
      use [⟨e₀,i⟩,q], dsimp [π], rw [hq, hx] },
    { intros a,
      dsimp [π], rw functor.map_comp,
      erw finsupp.map_domain_comp,
      apply key } },
end

instance Profinite.mono_free'_to_condensed_free_pfpng
  (S : Profinite.{u}) : mono S.free'_to_condensed_free_pfpng :=
begin
  apply presheaf_to_Condensed_Ab_map_mono_of_exists, intros B t ht,
  let e : S.to_Condensed.val.obj (op B) →
    S.condensed_free_pfpng.val.obj (op B) :=
    λ f, (S.to_condensed_free_pfpng.val.app (op B) f),
  dsimp at t ht,
  replace ht : free'_lift e t = 0, by rwa ← S.adj'_hom_equiv_symm_eq_free'_lift,
  let ι : Π b : B, S.to_Condensed.val.obj (op B) → S :=
    λ b f, (ulift.down f).1 b,
  have aux : ∀ b : B, t.map_domain (ι b) = 0 :=
    λ b, S.specialization_eq_zero_of_eq_zero B b t ht,
  dsimp,
  apply Profinite.mono_free'_to_condensed_free_pfpng_induction_aux,
  refl,
  assumption',
end

instance Condensed_Ab_to_CondensedSet_faithful :
  faithful Condensed_Ab_to_CondensedSet :=
{ map_injective' := begin
    intros X Y f g h, ext W t : 4,
    apply_fun (λ e, e.val.app W t) at h, dsimp at h,
    exact h
  end }

lemma category_theory.epi_to_colimit_of_exists {J : Type u}
  [small_category J] {C : Type*} [category.{u} C]
  {F : J ⥤ C} (T : C)
  (E : limits.cocone F) (hE : limits.is_colimit E)
  (f : T ⟶ E.X)
  (h : ∀ j : J,
    ∃ (Z : C) (p : Z ⟶ T) (q : Z ⟶ F.obj j) (hq : epi q),
      q ≫ E.ι.app j = p ≫ f) : epi f :=
begin
  constructor, intros W a b hh,
  apply hE.hom_ext, intros j, specialize h j,
  obtain ⟨Z,p,q,hq,w⟩ := h, resetI,
  rw ← cancel_epi q, simp_rw [← category.assoc, w,
    category.assoc, hh],
end

lemma epi_Profinite_to_Condensed_map_of_epi {X Y : Profinite.{u}}
  (f : X ⟶ Y) [hf : epi f] : epi (Profinite_to_Condensed.map f) :=
begin
  constructor, intros Z a b h, ext W q : 34, induction W using opposite.rec,
  have hZ := Z.2,
  rw is_sheaf_iff_is_sheaf_of_type at hZ,
  rw Z.val.is_proetale_sheaf_of_types_tfae.out 0 1 at hZ,
  let q' := q.down,
  dsimp at q q',
  dsimp [functor.is_proetale_sheaf_of_types] at hZ,
  specialize hZ punit W (λ _, Profinite.pullback f q')
    (λ _, Profinite.pullback.snd _ _) _ _,
  { intro w,
    rw Profinite.epi_iff_surjective at hf,
    obtain ⟨x, hx⟩ := hf (q' w),
    refine ⟨punit.star, ⟨(x, w), hx⟩, rfl⟩, },
  { intros i, dsimp, refine Z.val.map _ (b.val.app (op W) q),
    refine quiver.hom.op _, exact Profinite.pullback.snd _ _ },
  specialize hZ _,
  { clear hZ,
    rintro ⟨⟩ ⟨⟩ S g₁ g₂ H, dsimp only at H,
    apply_fun (λ φ, Z.val.map φ.op (b.val.app (op W) q)) at H,
    simp only [op_comp, Z.val.map_comp] at H, exact H, },
  obtain ⟨t,ht1,ht2⟩ := hZ,
  have : b.val.app (op W) q = t,
  { apply ht2,
    intros i, refl },
  rw this, apply ht2,
  intros i, dsimp,
  change (a.val.app (op W) ≫ Z.val.map _) q =
    (b.val.app (op W) ≫ Z.val.map _) q,
  simp only [← nat_trans.naturality],
  dsimp,
  apply_fun (λ e, Profinite_to_Condensed.map (Profinite.pullback.fst f q') ≫ e) at h,
  apply_fun (λ e, e.val.app (op (Profinite.pullback f q'))) at h,
  dsimp at h,
  let i : (Profinite.pullback f q').to_Condensed.val.obj (op (Profinite.pullback f q')) :=
    ulift.up (𝟙 _),
  apply_fun (λ e, e i) at h,
  dsimp [ulift_functor] at h,
  convert h,
  all_goals
  { ext1,
    dsimp [Profinite.to_Condensed],
    simp only [category.id_comp, Profinite.pullback.condition] },
end

inductive pmz : set ℤ
| neg_one : pmz (-1)
| zero : pmz 0
| one : pmz 1

def pmz_eq : pmz = {0,1,-1} :=
begin
  ext, split,
  { intros h, cases h, right, right, simpa, left, simp, right, left, simp },
  { intros h, simp at h, rcases h with (rfl|rfl|rfl),
    apply pmz.zero,
    apply pmz.one,
    apply pmz.neg_one }
end

lemma pmz_finite : set.finite pmz :=
by simp [pmz_eq]

instance fintype_pmz : fintype pmz := pmz_finite.fintype

--abbreviation Profinite.pow (S : Profinite.{u}) (n : ℕ) : Profinite.{u} :=
--Profinite.product (λ i : fin n, S)

/-- `S.profinite n` is `(S × {-1,0,1})^n`. -/
def Profinite.pmz (S : Profinite.{u}) (n : ℕ) : Profinite.{u} :=
Profinite.sigma $ λ (x : ulift.{u} (fin n → pmz)), S.pow n

/-- the canonical map of condensed sets `(S × {-1,0,1})^n ⟶ ℤ[S]` -/
def Profinite.pmz_to_free' (S : Profinite.{u}) (n : ℕ) :
  (S.pmz n).to_Condensed ⟶ Condensed_Ab_to_CondensedSet.obj S.free' :=
(Profinite.to_Condensed_equiv (S.pmz n) (Condensed_Ab_to_CondensedSet.obj S.free')).symm $
  (CondensedSet.val_obj_sigma_equiv (λ (f : ulift.{u} (fin n → pmz)), S.pow n)
    (Condensed_Ab_to_CondensedSet.obj S.free')).symm $
λ (f : ulift.{u} (fin n → pmz)),
let e := proetale_topology.to_sheafify (S.to_Condensed.val ⋙ AddCommGroup.free') in
e.app (op $ S.pow n) $ ∑ i : fin n, finsupp.single (ulift.up $ Profinite.product.π _ i) (f.down i)

def Profinite.pmz_functor (n : ℕ) : Profinite.{u} ⥤ Profinite.{u} :=
{ obj := λ S, S.pmz n,
  map := λ S T f,
    Profinite.sigma.desc _ $ λ e,
      (Profinite.product.lift (λ i : fin n, T)
        (λ i, Profinite.product.π _ i ≫ f)) ≫ Profinite.sigma.ι _ e,
  map_id' := begin
    intros X,
    apply Profinite.sigma.hom_ext, intros e,
    erw category.comp_id, refl,
  end,
  map_comp' := begin
    intros X Y Z f g,
    apply Profinite.sigma.hom_ext, intros e, dsimp, simp,
    erw [Profinite.sigma.ι_desc],
    refl,
  end }

def Profinite.pmz_diagram (S : Profinite.{u}) (n : ℕ) :
  discrete_quotient S ⥤ Profinite.{u} :=
S.diagram ⋙ Profinite.pmz_functor n

def Profinite.pmz_cone (S : Profinite.{u}) (n : ℕ) : limits.cone (S.pmz_diagram n) :=
(Profinite.pmz_functor n).map_cone S.as_limit_cone

def Profinite.sigma_functor {J : Type u} [small_category J]
  (F : J ⥤ Profinite.{u}) (α : Type u) [fintype α] :
  J ⥤ Profinite.{u} :=
{ obj := λ j, Profinite.sigma (λ a : α, F.obj j),
  map := λ i j e, Profinite.sigma.desc _ $ λ a,
    F.map e ≫ Profinite.sigma.ι _ a,
  map_id' := begin
    intros j, apply Profinite.sigma.hom_ext, intros a,
    simp,
  end,
  map_comp' := begin
    intros i j k e f,
    apply Profinite.sigma.hom_ext, intros a,
    simp,
  end }

def Profinite.sigma_cone {J : Type u} [small_category J]
  {F : J ⥤ Profinite.{u}} (α : Type u) [fintype α]
  (E : limits.cone F) :
  limits.cone (Profinite.sigma_functor F α) :=
{ X := Profinite.sigma (λ a : α, E.X),
  π :=
  { app := λ j, Profinite.sigma.desc _ $ λ a,
      E.π.app j ≫ Profinite.sigma.ι _ a,
    naturality' := begin
      intros i j e, dsimp,
      apply Profinite.sigma.hom_ext, intros a,
      simp, dsimp [Profinite.sigma_functor], simp,
    end } }

def Profinite.sigma_to_limit {J : Type u} [small_category J]
  (F : J ⥤ Profinite.{u}) (α : Type u) [fintype α]
  (E : limits.cone F) :
  (Profinite.sigma_cone α E).X ⟶
    (Profinite.limit_cone (Profinite.sigma_functor F α)).X :=
Profinite.sigma.desc _ $ λ a, (Profinite.limit_cone_is_limit
  (Profinite.sigma_functor F α)).lift ⟨E.X,
  { app := λ j, E.π.app j ≫ Profinite.sigma.ι _ a,
  naturality' := begin
    intros i j e, dsimp [Profinite.sigma_functor],
    simp,
  end }⟩

lemma Profinite.exists_of_sigma_limit {J : Type u} [small_category J]
  (F : J ⥤ Profinite.{u}) (α : Type u) [fintype α] [is_cofiltered J]
  (t : (Profinite.limit_cone (Profinite.sigma_functor F α)).X) :
  ∃ (a₀ : α) (t₀ : (Profinite.limit_cone F).X),
    ∀ j : J, Profinite.sigma.ι _ a₀
      ((Profinite.limit_cone F).π.app j t₀) =
      (Profinite.limit_cone (Profinite.sigma_functor F α)).π.app j t :=
begin
  rcases t with ⟨t,ht⟩, dsimp at ht,
  obtain ⟨j₀⟩ : nonempty J := is_cofiltered.nonempty,
  let a₀ := (t j₀).1, use a₀,
  have h1 : ∀ ⦃i j : J⦄ (f : i ⟶ j), (t i).1 = (t j).1,
  { intros i j e, specialize ht e,
    apply_fun (λ q, q.1) at ht,
    cases t i, exact ht },
  have h2 : ∀ j : J, (t j).1 = a₀,
  { intros j,
    let j₁ := is_cofiltered.min j j₀,
    rw ← h1 (is_cofiltered.min_to_left j j₀), dsimp [a₀],
    rw ← h1 (is_cofiltered.min_to_right j j₀) },
  let t₀ : (Profinite.limit_cone F).X := ⟨_,_⟩,
  rotate,
  { intros j, exact (t j).2 },
  { intros i j e,
    specialize ht e,
    cases (t i),
    dsimp [Profinite.sigma_functor, Profinite.sigma.desc, Profinite.sigma.ι] at ht,
    cases t j,
    erw sigma.mk.inj_iff at ht,
    exact eq_of_heq ht.2 },
  use t₀,
  intros j,
  dsimp [Profinite.limit_cone, Profinite.sigma_functor, Profinite.sigma.ι,
    Profinite.sigma.desc, CompHaus.limit_cone, Top.limit_cone], ext,
  exact (h2 _).symm, refl,
end

lemma Profinite.bijective_sigma_to_limit {J : Type u} [small_category J]
  (F : J ⥤ Profinite.{u}) (α : Type u) [fintype α]
  (E : limits.cone F) (hE : limits.is_limit E) [is_cofiltered J] :
  function.bijective (Profinite.sigma_to_limit F α E) :=
begin
  split,
  { rintros ⟨a,x⟩ ⟨b,y⟩ h,
    dsimp [Profinite.sigma_to_limit, Profinite.sigma.desc,
      Profinite.limit_cone_is_limit, CompHaus.limit_cone_is_limit,
      Top.limit_cone_is_limit] at h,
    apply_fun (λ e, e.1) at h,
    have hh := h,
    obtain ⟨j₀⟩ : nonempty J := is_cofiltered.nonempty,
    apply_fun (λ e, (e j₀).1) at h, dsimp [Profinite.sigma.ι] at h,
    subst h, ext, refl,
    apply heq_of_eq,
    apply limits.concrete.is_limit_ext _ hE,
    intros jj, apply_fun (λ e, e jj) at hh,
    erw sigma.mk.inj_iff at hh,
    exact eq_of_heq hh.2 },
  { rintros t,
    obtain ⟨a,s,ht⟩ := Profinite.exists_of_sigma_limit F α t,
    use a, let EE : E.X ≅ (Profinite.limit_cone F).X :=
      hE.cone_point_unique_up_to_iso (Profinite.limit_cone_is_limit _),
    use EE.inv s, dsimp, ext j : 2,
    convert ht j, ext, refl,
    apply heq_of_eq,
    change ((hE.lift (Profinite.limit_cone F)) ≫ E.π.app j) s = _,
    rw hE.fac, refl }
end

lemma Profinite.is_iso_lift_sigma_cone {J : Type u} [small_category J]
  {F : J ⥤ Profinite.{u}} (α : Type u) [fintype α] [is_cofiltered J]
  (E : limits.cone F) (hE : limits.is_limit E) :
  is_iso ((Profinite.limit_cone_is_limit _).lift (Profinite.sigma_cone α E)) :=
begin
  apply Profinite.is_iso_of_bijective,
  convert Profinite.bijective_sigma_to_limit F α E hE,
  symmetry,
  apply (Profinite.limit_cone_is_limit (Profinite.sigma_functor F α)).uniq,
  intros j,
  apply Profinite.sigma.hom_ext,
  intros a, refl,
end

def Profinite.sigma_cone_is_limit {J : Type u} [small_category J]
  {F : J ⥤ Profinite.{u}} (α : Type u) [fintype α] [is_cofiltered J]
  (E : limits.cone F) (hE : limits.is_limit E) :
  limits.is_limit (Profinite.sigma_cone α E) :=
begin
  haveI : is_iso ((Profinite.limit_cone_is_limit _).lift (Profinite.sigma_cone α E)) :=
    Profinite.is_iso_lift_sigma_cone α E hE,
  apply limits.is_limit.of_point_iso (Profinite.limit_cone_is_limit _),
  assumption
end

def Profinite.pmz_to_limit (S : Profinite.{u}) (n : ℕ) :
  S.pmz n ⟶ (Profinite.limit_cone (S.pmz_diagram n)).X :=
Profinite.sigma.desc _ $ λ f,
  (Profinite.limit_cone_is_limit (S.pmz_diagram n)).lift ⟨S.pow n,
  { app := λ T, Profinite.map_pow (S.as_limit_cone.π.app T) n ≫
      Profinite.sigma.ι _ f,
    naturality' := sorry }⟩

def Profinite.pow_functor (n : ℕ) : Profinite.{u} ⥤ Profinite.{u} :=
{ obj := λ S, S.pow n,
  map := λ S T f, Profinite.map_pow f n,
  map_id' := sorry,
  map_comp' := sorry }

def Profinite.pow_cone {J : Type u} [small_category J] {F : J ⥤ Profinite.{u}}
  (E : limits.cone F) (n : ℕ) : limits.cone (F ⋙ Profinite.pow_functor n) :=
(Profinite.pow_functor n).map_cone E

def Profinite.pow_cone_is_limit
  {J : Type u} [small_category J] {F : J ⥤ Profinite.{u}}
  (E : limits.cone F) (hE : limits.is_limit E) (n : ℕ) :
  limits.is_limit (Profinite.pow_cone E n) :=
{ lift := λ Q, Profinite.product.lift _ $ λ a,
    hE.lift ⟨Q.X,
    { app := λ j, Q.π.app j ≫ Profinite.product.π _ a,
      naturality' := sorry }⟩,
  fac' := sorry,
  uniq' := sorry }

lemma Profinite.is_iso_pmz_to_limit (S : Profinite.{u}) (n : ℕ) :
  is_iso (S.pmz_to_limit n) :=
begin
  let E := Profinite.sigma_cone (ulift.{u} (fin n → pmz))
    (Profinite.pow_cone S.as_limit_cone n),
  let hE : limits.is_limit E := Profinite.sigma_cone_is_limit _ _
    (Profinite.pow_cone_is_limit _ S.as_limit n),
  let q : E.X ≅ (Profinite.limit_cone (S.pmz_diagram n)).X :=
    hE.cone_point_unique_up_to_iso (Profinite.limit_cone_is_limit _),
  have : is_iso q.hom := infer_instance,
  convert this,
  apply Profinite.sigma.hom_ext, intros e,
  apply (Profinite.limit_cone_is_limit _).hom_ext,
  intros T,
  refl,
end

def Profinite.pmz_cone_is_limit (S : Profinite.{u}) (n : ℕ) :
  limits.is_limit (S.pmz_cone n) :=
begin
  apply limits.is_limit.of_point_iso (Profinite.limit_cone_is_limit _),
  convert Profinite.is_iso_pmz_to_limit S n,
  apply Profinite.sigma.hom_ext, intros a,
  apply (Profinite.limit_cone_is_limit _).hom_ext, intros j,
  refl,
end

instance Profinite.discrete_topology_discrete_quotient_pmz
  (S : Profinite.{u}) (n : ℕ) (T : discrete_quotient S) :
  discrete_topology ((Profinite.of T).pmz n) := sorry

instance Profinite.discrete_topology_discrete_quotient_pow
  (S : Profinite.{u}) (n : ℕ) (T : discrete_quotient S) :
  discrete_topology ((Profinite.of T).pow n) := sorry

def Profinite.pmz_to_level_component (S : Profinite.{u}) (j : nnreal) (T : discrete_quotient S)
  (e : fin ⌊j⌋₊ → pmz) :
  (Profinite.of ↥T).pow ⌊j⌋₊ ⟶
  (ProFiltPseuNormGrp₁.level.obj j).obj (free_pfpng_functor.obj (Fintype.of ↥T)) :=
{ to_fun := λ t,
  { val := ∑ i : fin ⌊j⌋₊, (λ s, if t i = s then e i else 0),
    property := sorry },
  continuous_to_fun := continuous_of_discrete_topology }

def Profinite.pmz_to_level (S : Profinite.{u}) (j : nnreal) (T : discrete_quotient S) :
  (Profinite.of T).pmz ⌊j⌋₊ ⟶
    (ProFiltPseuNormGrp₁.level.obj j).obj (free_pfpng_functor.obj $ Fintype.of T) :=
{ to_fun := Profinite.sigma.desc _ $ λ e, S.pmz_to_level_component j T (ulift.down e),
  continuous_to_fun := continuous_of_discrete_topology }

def Profinite.pmz_to_level_nat_trans (S : Profinite.{u}) (j : nnreal) :
  S.pmz_diagram ⌊j⌋₊ ⟶ (S.fintype_diagram ⋙ free_pfpng_functor) ⋙
    (ProFiltPseuNormGrp₁.level.obj j) :=
{ app := λ T, S.pmz_to_level j T,
  naturality' := sorry }

def Profinite.pmz_to_free_pfpng (S : Profinite.{u}) (j : nnreal) :
  S.pmz ⌊j⌋₊ ⟶ (ProFiltPseuNormGrp₁.level.obj j).obj S.free_pfpng :=
let E := limits.is_limit_of_preserves (ProFiltPseuNormGrp₁.level.obj j)
  (limits.limit.is_limit (S.fintype_diagram ⋙ free_pfpng_functor)) in
E.map (S.pmz_cone _) (S.pmz_to_level_nat_trans j)

lemma Profinite.is_limit.surjective_of_surjective
  {J : Type u} [small_category J] (F G : J ⥤ Profinite.{u})
  (α : F ⟶ G) (cF : limits.cone F)
  (cG : limits.cone G) (hcF : limits.is_limit cF) (hcG : limits.is_limit cG)
  [is_cofiltered J] (surj : ∀ (j : J), function.surjective ⇑(α.app j)) :
  function.surjective ⇑(limits.is_limit.map cF hcG α) :=
begin
  have := CompHaus.is_limit.surjective_of_surjective
    (F ⋙ Profinite_to_CompHaus)
    (G ⋙ Profinite_to_CompHaus)
    (whisker_right α _)
    (Profinite_to_CompHaus.map_cone cF)
    (Profinite_to_CompHaus.map_cone cG)
    (limits.is_limit_of_preserves _ hcF)
    (limits.is_limit_of_preserves _ hcG)
    surj,
  change function.surjective
    (Profinite_to_CompHaus.map (limits.is_limit.map cF hcG α)),
  convert this,
  apply hcG.hom_ext, intros j,
  simp only [limits.is_limit.map_π, iso.trans_hom, iso.symm_hom,
    functor.map_iso_hom, limits.is_limit.unique_up_to_iso_hom,
    limits.cone.category_comp_hom, limits.is_limit.lift_cone_morphism_hom,
    limits.limit.is_limit_lift, limits.cones.functoriality_map_hom,
    Profinite_to_CompHaus_map],
  erw [category.assoc, category.assoc],
  erw hcG.fac,
  have := (lifted_limit_maps_to_original
    (limits.limit.is_limit (G ⋙ Profinite_to_CompHaus))).inv.w j,
  erw this,
  dsimp, simp only [limits.limit.lift_π, limits.cones.postcompose_obj_π,
    nat_trans.comp_app, functor.map_cone_π_app,
    Profinite_to_CompHaus_map, whisker_right_app],
  refl,
end

instance Profinite.pmz_to_free_pfpng_epi (S : Profinite.{u}) (j : nnreal) :
  epi (S.pmz_to_free_pfpng j) :=
begin
  rw Profinite.epi_iff_surjective,
  dsimp only [Profinite.pmz_to_free_pfpng],
  have := Profinite.is_limit.surjective_of_surjective _ _ (S.pmz_to_level_nat_trans j)
    (S.pmz_cone _)
    ((ProFiltPseuNormGrp₁.level.obj j).map_cone (limits.limit.cone _))
    (S.pmz_cone_is_limit _)
    (limits.is_limit_of_preserves _ (limits.limit.is_limit _)),
  apply this,
  intros T,
  /-
  We have now reduced to the finite case, where `pmz_to_free_pfpng` has an
  explicit description.
  -/

  sorry
end

instance Profinite.epi_free'_to_condensed_free_pfpng
  (S : Profinite.{u}) : epi S.free'_to_condensed_free_pfpng :=
begin
  apply faithful_reflects_epi (Condensed_Ab_to_CondensedSet),
  let E := CompHausFiltPseuNormGrp.level_Condensed_diagram_cocone
    (CompHausFiltPseuNormGrp₁.enlarging_functor.obj
    ((ProFiltPseuNormGrp₁.to_CHFPNG₁.obj S.free_pfpng))),
  have hh : is_iso (limits.colimit.desc _ E),
  { change is_iso (CompHausFiltPseuNormGrp.colimit_to_Condensed_obj _),
    apply_instance },
  let hE : limits.is_colimit E := @limits.is_colimit.of_point_iso
    _ _ _ _ _ _ _ _ hh, -- <-- move this
  apply category_theory.epi_to_colimit_of_exists  _ E hE,
  intros j,
  let j' : nnreal := ulift.down j,
  use [(S.pmz ⌊j'⌋₊).to_Condensed, S.pmz_to_free' ⌊j'⌋₊,
    Profinite_to_Condensed.map (S.pmz_to_free_pfpng j')],
  split,
  { apply epi_Profinite_to_Condensed_map_of_epi },
  { sorry }
end

instance Profinite.is_iso_free'_to_condensed_free_pfpng
  (S : Profinite.{u}) : is_iso S.free'_to_condensed_free_pfpng :=
is_iso_of_mono_of_epi _

def Profinite.free_to_pfpng (S : Profinite.{u}) :
  CondensedSet_to_Condensed_Ab.obj S.to_Condensed ⟶
  S.condensed_free_pfpng :=
(Condensed_Ab_CondensedSet_adjunction.hom_equiv _ _).symm S.to_condensed_free_pfpng

attribute [simps hom_app] AddCommGroup.free_iso_free'

instance Profinite.is_iso_free_to_pfpng (S : Profinite.{u}) : is_iso S.free_to_pfpng :=
begin
  suffices : S.free_to_pfpng =
    (CondensedSet_to_Condensed_Ab_iso.app S.to_Condensed).hom ≫
    S.free'_to_condensed_free_pfpng,
  { rw this, apply_instance },
  rw [iso.app_hom],
  delta Profinite.free'_to_condensed_free_pfpng Profinite.free'_lift Profinite.free_to_pfpng
    CondensedSet_to_Condensed_Ab_iso Sheaf.adjunction
    Condensed_Ab_CondensedSet_adjunction Condensed_Ab_CondensedSet_adjunction',
  ext T : 4,
  dsimp only [adjunction.mk_of_hom_equiv_hom_equiv, functor.map_iso_hom, quiver.hom.forget_Ab,
    Sheaf.hom.comp_val, Condensed_Ab_to_CondensedSet_map, Sheaf.compose_equiv_symm_apply_val,
    presheaf_to_Sheaf_map_val, nat_trans.comp_app,
    iso_whisker_left_hom, iso_whisker_right_hom, whisker_left_app, whisker_right_app],
  rw [← nat_trans.comp_app, sheafify_map_sheafify_lift],
  congr' 4, clear T,
  ext T : 2,
  dsimp only [whiskering_right_map_app_app, whiskering_right_obj_map, nat_trans.comp_app,
    adjunction.whisker_right, adjunction.mk_of_unit_counit_hom_equiv_symm_apply,
    whisker_left_app, whisker_right_app,
    functor.associator_hom_app, functor.right_unitor_hom_app],
  erw [category.id_comp, category.id_comp, category.comp_id, category.comp_id],
  rw [← nat_trans.naturality_assoc],
  congr' 1,
  dsimp only [AddCommGroup.adj, AddCommGroup.adj', adjunction.mk_of_hom_equiv_hom_equiv,
    adjunction.of_nat_iso_left, adjunction.mk_of_hom_equiv_counit_app,
    equiv.inv_fun_as_coe, equiv.symm_trans_apply, iso.symm_hom,
    adjunction.equiv_homset_left_of_nat_iso_symm_apply],
  simp only [equiv.symm_symm],
  erw [← category.assoc, ← nat_trans.comp_app, iso.hom_inv_id, nat_trans.id_app,
    category.id_comp],
end

def free_pfpng_profinite_natural_map :
  Profinite_to_Condensed ⋙ CondensedSet_to_Condensed_Ab ⟶
  Profinite.extend free_pfpng_functor ⋙
  ProFiltPseuNormGrp₁.to_CHFPNG₁ ⋙
  CompHausFiltPseuNormGrp₁.enlarging_functor ⋙
  CompHausFiltPseuNormGrp.to_Condensed :=
{ app := λ X, X.free_to_pfpng,
  naturality' := λ S T f, begin
    -- we should be able to precompose with the natural map `S.to_Condensed ⟶ S.free'`
    -- how do we do that?
    sorry
  end }
/-
whisker_right profinite_to_condensed_unit _ ≫
(functor.associator _ _ _).hom ≫
whisker_left _ (
  (functor.associator _ _ _).hom ≫
  whisker_left _ (
    (functor.associator _ _ _).hom ≫
    whisker_left _ (
      (functor.associator _ _ _).hom ≫ whisker_left _
        Condensed_Ab_CondensedSet_adjunction.counit ≫ (functor.right_unitor _).hom )))
-/

/-
def profinite_to_condensed_unit :
  Profinite_to_Condensed ⟶
  condensify (free_pfpng_functor ⋙ ProFiltPseuNormGrp₁.to_CHFPNG₁) ⋙
    Condensed_Ab_to_CondensedSet :=
{ app := λ S, S.to_free_pfpng' ≫ _,
  naturality' := sorry }

def free_pfpng_profinite_natural_map :
  Profinite_to_Condensed ⋙ CondensedSet_to_Condensed_Ab ⟶
  condensify (free_pfpng_functor ⋙ ProFiltPseuNormGrp₁.to_CHFPNG₁) :=
(((whiskering_right _ _ _).obj CondensedSet_to_Condensed_Ab).map profinite_to_condensed_unit) ≫
  whisker_left
    (condensify (free_pfpng_functor ⋙ ProFiltPseuNormGrp₁.to_CHFPNG₁))
    Condensed_Ab_CondensedSet_adjunction.counit
-/

instance free_pfpng_profinite_natural_map_is_iso :
  is_iso free_pfpng_profinite_natural_map :=
begin
  apply_with nat_iso.is_iso_of_is_iso_app { instances := ff },
  intros X,
  apply X.is_iso_free_to_pfpng,
end

/-- Prop 2.1 of Analytic.pdf -/
def free_pfpng_profinite_iso :
  condensify (free_pfpng_functor ⋙ ProFiltPseuNormGrp₁.to_CHFPNG₁) ≅
  Profinite_to_Condensed ⋙ CondensedSet_to_Condensed_Ab :=
sorry ≪≫ (as_iso free_pfpng_profinite_natural_map).symm

.

-- #check Condensed_Ab_CondensedSet_adjunction
