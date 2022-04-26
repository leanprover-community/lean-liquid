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
