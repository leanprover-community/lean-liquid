import free_pfpng.basic
import condensed.projective_resolution
import condensed.condensify
import condensed.adjunctions
import condensed.sheafification_mono
import free_pfpng.lemmas

import for_mathlib.int

.


noncomputable theory

open category_theory
open opposite

-- jmc: This is maybe not the best way to set things up.
-- The counit in `free_pfpng_profinite_natural_map` will probably be annoying

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
    S.to_free_pfpng.2.comp (ulift.down f).2 ,rfl⟩ :=
rfl

def profinite_to_condensed_unit :
  Profinite_to_Condensed ⟶
  Profinite.extend free_pfpng_functor ⋙
  ProFiltPseuNormGrp₁.to_CHFPNG₁ ⋙
  CompHausFiltPseuNormGrp₁.enlarging_functor ⋙
  CompHausFiltPseuNormGrp.to_Condensed ⋙
  Condensed_Ab_to_CondensedSet :=
{ app := λ S, S.to_condensed_free_pfpng,
  naturality' := sorry }

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

def Profinite.condensed_free_pfpng_specialize_cone (S B : Profinite.{u}) (b : B) :
  limits.cone ((S.fintype_diagram ⋙ forget Fintype ⋙ AddCommGroup.free') ⋙ Ab.ulift.{u+1}) :=
{ X := S.condensed_free_pfpng.val.obj (op B),
  π :=
  { app := λ T,
    { to_fun := λ t, ⟨finsupp.equiv_fun_on_fintype.symm (S.free_pfpng_π T (t.down.1 b))⟩,
      map_zero' := sorry,
      map_add' := sorry },
    naturality' := sorry } }

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

def ProFiltPseuNormGroup₁.limit_π_coe_eq
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
    erw ProFiltPseuNormGroup₁.limit_π_coe_eq,
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
  induction n,
  case nat.zero
  { intros S B t ht, simp at ht, rw ht, intros h1 h2,
    use [punit, infer_instance, λ _, B, λ _, 𝟙 _],
    split, { intros b, use [punit.star, b], refl },
    { intros _, rw finsupp.map_domain_zero, } },
  case nat.succ : n hn
  { intros S B t ht1 ht2 H,
    by_cases ht2' : t.support.card = n+1, swap, { sorry }, clear ht2,
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
      -- extract out of `H` two functions `g₁ g₂ : B ⟶ S` with `g₁ ≠ g₂` and `g₁ b = g₂ b`
      sorry },

    let f₀ : Π (i : E₀), S.to_Condensed.val.obj (op B) → S.to_Condensed.val.obj (op (X₀ i)) :=
      λ i, S.to_Condensed.val.map (π₀ i).op,

    let t₀ : Π (i : E₀), S.to_Condensed.val.obj (op (X₀ i)) →₀ ℤ :=
      λ i, t.map_domain (f₀ i),

    have card₀ : ∀ (i : E₀), (t₀ i).support.card ≤ n := sorry,
    have lift₀ : ∀ (i : E₀), free'_lift (S.to_condensed_free_pfpng.val.app (op (X₀ i))) (t₀ i) = 0,
      sorry,

    have map₀ : ∀ (i : E₀) (b : ↥(X₀ i)),
        finsupp.map_domain
          (λ (f : S.to_Condensed.val.obj (op (X₀ i))), f.down.to_fun b) (t₀ i) = 0, sorry,
    have key := λ i, hn S (X₀ i) (t₀ i) (card₀ i) (lift₀ i) (map₀ i),

    choose A hA X₁ π₁ surj₁ key using key, resetI,

    let E := Σ (e : E₀), A e,
    let X : E → Profinite.{u} := λ i, X₁ i.1 i.2,
    let π : Π (e : E), X e ⟶ B := λ e, π₁ e.1 e.2 ≫ π₀ e.1,

    use [E, infer_instance, X, π], split,

    { sorry },
    { sorry },
  },
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

instance Profinite.epi_free'_to_condensed_free_pfpng
  (S : Profinite.{u}) : epi S.free'_to_condensed_free_pfpng := sorry

instance Profinite.is_iso_free'_to_condensed_free_pfpng
  (S : Profinite.{u}) : is_iso S.free'_to_condensed_free_pfpng :=
is_iso_of_mono_of_epi _

def Profinite.free_to_pfpng (S : Profinite.{u}) :
  CondensedSet_to_Condensed_Ab.obj S.to_Condensed ⟶
  S.condensed_free_pfpng :=
(Condensed_Ab_CondensedSet_adjunction.hom_equiv _ _).symm S.to_condensed_free_pfpng

instance Profinite.is_iso_free_to_pfpng (S : Profinite.{u}) : is_iso S.free_to_pfpng :=
begin
  suffices : S.free_to_pfpng =
    (CondensedSet_to_Condensed_Ab_iso.app S.to_Condensed).hom ≫
    S.free'_to_condensed_free_pfpng,
  { rw this, apply_instance },
  sorry
end

def free_pfpng_profinite_natural_map :
  Profinite_to_Condensed ⋙ CondensedSet_to_Condensed_Ab ⟶
  Profinite.extend free_pfpng_functor ⋙
  ProFiltPseuNormGrp₁.to_CHFPNG₁ ⋙
  CompHausFiltPseuNormGrp₁.enlarging_functor ⋙
  CompHausFiltPseuNormGrp.to_Condensed :=
{ app := λ X, X.free_to_pfpng,
  naturality' := sorry }
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
