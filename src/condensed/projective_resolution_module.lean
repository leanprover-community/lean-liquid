import condensed.ab
import condensed.top_comparison
import condensed.adjunctions_module
import condensed.extr.equivalence
import category_theory.sites.limits
import algebra.category.Group.filtered_colimits

import for_mathlib.abelian_category
import for_mathlib.ab_epi

universe u

open category_theory

/-

S extr. disc.
A cond ab group.

A ↦ Hom_{CondSet}(S,A) = A(S) commutes with limits and colimits.

A(-) commutes with finite products, in Ab, finite products = finite coproducts.

Z[S] is projective.

A -> B epi, Hom(Z[S],A) -> Hom(Z[S],B) -- A(S) -> B(S) WTS: surjective.

1. If S is extr. disc. and A -> B is an epi of cond ab, then A(S) -> B(S) surjective.
  B -> B/A

-/

noncomputable theory

variables (R : Type (u + 1)) [comm_ring R]

def CondensedMod.free (S : CondensedSet) : CondensedMod R :=
(CondensedSet_to_CondensedMod R).obj $ S

local notation R`[`S`]` := CondensedMod.free R S.to_Condensed

variable {R}

def Condensed.forgetMod (S : CondensedMod R) : CondensedSet :=
(CondensedMod_to_CondensedSet R).obj S

def quiver.hom.forgetMod {S T : CondensedMod R} (e : S ⟶ T) :
  S.forgetMod ⟶ T.forgetMod :=
(CondensedMod_to_CondensedSet R).map e

variable (R)

namespace CondensedMod

def to_free (S : CondensedSet) : S ⟶ (free R S).forgetMod :=
(CondensedMod_CondensedSet_adjunction R).hom_equiv _ _ $ 𝟙 _

def free_lift {S : CondensedSet} {A : CondensedMod R} (e : S ⟶ A.forgetMod) :
  free R S ⟶ A :=
((CondensedMod_CondensedSet_adjunction R).hom_equiv _ _).symm e

@[simp]
lemma to_free_free_lift {S : CondensedSet} {A : CondensedMod R} (e : S ⟶ A.forgetMod) :
  to_free R S ≫ (free_lift R e).forgetMod = e :=
begin
  dsimp only [Condensed.forgetMod, to_free, free_lift, quiver.hom.forgetMod],
  rw [adjunction.hom_equiv_unit, adjunction.hom_equiv_counit, category.assoc,
    category_theory.functor.map_id, category.id_comp, functor.map_comp,
    (CondensedMod_CondensedSet_adjunction R).unit_naturality_assoc,
    adjunction.right_triangle_components, category.comp_id],
end

lemma free_lift_unique {S : CondensedSet} {A : CondensedMod R}
  (e : S ⟶ A.forgetMod) (f : free R S ⟶ A)
  (h : to_free R S ≫ f.forgetMod = e) : f = free_lift R e :=
begin
  apply_fun ((CondensedMod_CondensedSet_adjunction R).hom_equiv _ _),
  dsimp [free_lift],
  rw equiv.apply_symm_apply,
  exact h
end

@[ext]
lemma free_hom_ext {S : CondensedSet} {A : CondensedMod R} (f g : free R S ⟶ A)
  (h : to_free R S ≫ f.forgetMod = to_free R S ≫ g.forgetMod) : f = g :=
by rw [free_lift_unique _ _ f rfl, free_lift_unique _ _ g rfl, h]

end CondensedMod

@[simps]
def hom_equiv_evaluation_Mod (S : Profinite.{u}) (A : CondensedMod R) :
  (R[S] ⟶ A) ≃ ((CondensedMod_to_CondensedSet R ⋙ CondensedSet.evaluation S).obj A) :=
((CondensedMod_CondensedSet_adjunction R).hom_equiv S.to_Condensed A).trans $
  (equiv_of_fully_faithful $ Sheaf_to_presheaf.{u} _ _).trans $ yoneda'_equiv _ _ .

lemma hom_equiv_evaluation_Mod_apply_eq_app_id (S : Profinite.{u}) (A : CondensedMod R)
  (f : R[S] ⟶ A) : hom_equiv_evaluation_Mod R S A f =
  (CondensedMod.to_free R _ ≫ (CondensedMod_to_CondensedSet R).map f).val.app _ ⟨𝟙 _⟩ := rfl

open_locale big_operators
lemma exists_hom_equiv_Mod_evaluation_symm_app_eq
  (S : Profinite.{u}) (A : CondensedMod R)
  (f : A.val.obj (opposite.op S)) : ∃ (t : R[S].val.obj (opposite.op S)),
  ((hom_equiv_evaluation_Mod R S A).symm f).val.app _ t = f :=
begin
  -- This proof can probably be made simpler using some adjunction voodoo...
  use (hom_equiv_evaluation_Mod _ _ _) (𝟙 _),
  dsimp [hom_equiv_evaluation_Mod, adjunction.whisker_right],
  simp_rw [← comp_apply, ← nat_trans.comp_app],
  erw [category.comp_id, proetale_topology.to_sheafify_sheafify_lift],
  dsimp [functor.preimage, full.preimage, yoneda'_equiv, CondensedMod_to_CondensedSet,
    functor.right_unitor, ulift_functor, Profinite.to_Condensed],
  sorry

  --dsimp [functor.preimage, full.preimage, yoneda'_equiv, Module.adj,
  --  functor.right_unitor, finsupp.map_domain],

  /-
  simp only [comp_apply, Module.free_map_coe, category.id_comp, category.comp_id],
  dsimp [functor.right_unitor, AddCommGroup.adj, applicative.to_functor],
  erw equiv.apply_symm_apply,
  simp,
  change _ + _ = _,
  rw zero_add,
  refl,
  -/
end

local attribute [instance] limits.has_zero_object.has_zero

open category_theory.limits
open opposite

-- sanity check
example (S : Profinite.{u}) : preserves_zero_objects
  (Condensed.evaluation (Module.{u+1} R) S) :=
infer_instance

instance projective_free_CondensedMod (S : Profinite.{u}) [projective S] :
  projective (R[S]) :=
{ factors := λ A B f g hg, begin
    rw epi_iff_is_zero_cokernel at hg,
    -- this follows from the fact that evaluation preserves colimits.
    let e : (cokernel g).val.obj (op S) ≅ cokernel (g.val.app (op S)) := begin
      refine (is_colimit_of_preserves (Condensed.evaluation (Module R) S)
      (colimit.is_colimit _)).cocone_point_unique_up_to_iso
        (colimit.is_colimit _) ≪≫ has_colimit.iso_of_nat_iso _,
      refine nat_iso.of_components _ _,
      { rintros (a|b), exact eq_to_iso rfl, exact eq_to_iso rfl },
      rintros (a|b) (c|d) (e|e),
      all_goals { dsimp },
      all_goals { simp, try { refl } },
    end,
    replace hg := is_zero_of_preserves (Condensed.evaluation (Module.{u+1} R) S) hg,
    dsimp [Condensed.evaluation] at hg,
    replace hg := is_zero_of_iso_of_zero hg e,
    rw ← epi_iff_is_zero_cokernel at hg,
    replace hg : function.surjective (g.val.app (op S)) := begin
      resetI,
      -- missing Module.surjective_of_epi
      --apply Module.surjective_of_epi,
      sorry
    end,
    let f₁ := hom_equiv_evaluation_Mod _ _ _ f,
    dsimp at f₁,
    obtain ⟨f',h⟩ := hg f₁,
    use (hom_equiv_evaluation_Mod _ _ _).symm f',
    apply_fun (hom_equiv_evaluation_Mod _ _ _),
    change _ = f₁,
    rw [← h, hom_equiv_evaluation_Mod_apply, Sheaf.hom.comp_val, nat_trans.comp_app],
    dsimp [hom_equiv_evaluation_Mod, adjunction.whisker_right, functor.associator],
    erw [category.id_comp, ← comp_apply, ← comp_apply, ← category.assoc, ← nat_trans.comp_app,
      ← nat_trans.comp_app],
    erw proetale_topology.to_sheafify_sheafify_lift,
    dsimp [functor.preimage, full.preimage, yoneda'_equiv, ulift_functor,
      CondensedMod_to_CondensedSet, Profinite.to_Condensed],
    -- same missing lemma as exists_hom_equiv_evaluation_symm_app_eq
    sorry

    --erw [← comp_apply, ← comp_apply, ← nat_trans.comp_app, ← nat_trans.comp_app],
    --erw proetale_topology.to_sheafify_sheafify_lift,
    /-
    simp_rw [← category.assoc, ← nat_trans.comp_app],
    rw adjunction.hom_equiv_counit,
    dsimp,
    simp only [category.assoc, adjunction.whisker_right_counit_app_app],
    simp_rw [comp_apply],
    congr' 1,
    dsimp [functor.preimage, yoneda'_equiv, full.preimage, AddCommGroup.adj, ulift_functor],
    change (free_abelian_group.lift id) (_ <$> free_abelian_group.of _) = _,
    simp,
    -/
  end } .

lemma is_zero_iff_forall_zero_Mod {A : CondensedMod R} :
  is_zero A ↔ ∀ (S : ExtrDisc), is_zero (A.val.obj (op S.val)) :=
begin
  split,
  { intros h S,
    apply is_zero_of_preserves (Condensed.evaluation (Module.{u+1} R) S.val),
    assumption },
  { intro h,
    let FF := ((Sheaf_to_presheaf _ _ : CondensedMod R ⥤ _) ⋙
      (whiskering_left _ _ _).obj (ExtrDisc_to_Profinite.op)),
    haveI : creates_colimits FF :=
      by apply Condensed_to_ExtrDisc_presheaf_creates_colimits,
    suffices : A ≅ ⊥_ _, by { apply is_zero_of_iso_of_zero _ this.symm, exact is_zero_initial },
    let e : Π S : ExtrDisc, (A.val.obj (op S.val)) ≅ ⊥_ _ :=
      λ S, is_zero.iso (h S) is_zero_initial,
    symmetry,
    apply (colimit.is_colimit _).cocone_point_unique_up_to_iso (_ : is_colimit (as_empty_cocone _)),
    apply is_colimit_of_reflects FF,
    apply evaluation_jointly_reflects_colimits,
    intros S,
    have := is_colimit_empty_cocone_equiv (Module R)
      (as_empty_cocone (A.val.obj (op S.unop.val)))
      (((evaluation ExtrDiscᵒᵖ (Module R)).obj S).map_cocone (FF.map_cocone (as_empty_cocone A)))
      (eq_to_iso rfl),
    apply this.to_fun,
    specialize e S.unop,
    let t : as_empty_cocone (A.val.obj (op (unop S).val)) ≅ as_empty_cocone (⊥_ _) :=
      cocones.ext e (by tidy),
    apply is_colimit.of_iso_colimit _ t.symm,
    refine ⟨λ r, _, _, _⟩,
    { dsimp, refine initial.to r.X, },
    { tidy },
    { tidy } }
end

lemma is_epi_iff_forall_surjective_Mod {A B : CondensedMod R} (f : A ⟶ B) :
  epi f ↔ ∀ (S : ExtrDisc), function.surjective (f.val.app (op S.val)) :=
begin
  rw epi_iff_is_zero_cokernel,
  rw is_zero_iff_forall_zero_Mod,
  apply forall_congr (λ S, _),
  let FF := Condensed.evaluation (Module.{u+1} R) S.val,
  haveI : preserves_colimits FF := infer_instance,
  let e : (cokernel f).val.obj (op S.val) ≅ cokernel (f.val.app (op S.val)) := begin
    change FF.obj (cokernel f) ≅ cokernel (FF.map f),
    change (FF.map_cocone _).X ≅ _,
    refine (is_colimit_of_preserves FF (colimit.is_colimit _)).cocone_point_unique_up_to_iso
      (colimit.is_colimit _) ≪≫ _,
    dsimp,
    apply has_colimit.iso_of_nat_iso,
    -- This isomorphism is probably somewhere in mathlib... or somewhere in this repo.
    refine nat_iso.of_components _ _,
    { rintros (i|i),
      { exact iso.refl _ },
      { exact iso.refl _ } },
    { rintros (i|i) (j|j) (f|f),
      { dsimp, simpa, },
      { dsimp, simp, },
      { dsimp, simpa, },
      { dsimp, simpa, } },
  end,
  have : is_zero ((cokernel f).val.obj (op S.val)) ↔ is_zero (cokernel (f.val.app (op S.val))),
  { split,
    { intro h, apply is_zero_of_iso_of_zero h e, },
    { intro h, apply is_zero_of_iso_of_zero h e.symm, } },
  rw [this, ← epi_iff_is_zero_cokernel],
  clear e,
  split,
  { introsI h,
    -- missing Module.surjective_of_epi,
    sorry },
  { intros h, exact concrete_category.epi_of_surjective (f.val.app (op S.val)) h}
end

theorem CondensedMod_has_enough_projectives_aux (A : CondensedMod R) :
  ∃ (B : CondensedMod R) (hB : projective B) (f : B ⟶ A), epi f :=
begin
  let II := Σ (S : ExtrDisc), A.val.obj (op S.val),
  let X : II → CondensedMod R := λ i, R[i.1.val],
  let f : Π i, X i ⟶ A := λ i, (hom_equiv_evaluation_Mod _ i.1.val A).symm i.2,

  -- Move this.
  haveI : has_colimits (CondensedMod R) := begin
    change has_colimits (Sheaf _ _),
    exact category_theory.Sheaf.category_theory.limits.has_colimits.{(u+2) u (u+1)},
  end,

  use [∐ X, infer_instance, sigma.desc f],

  rw is_epi_iff_forall_surjective_Mod,

  intros S t,
  obtain ⟨w,hw⟩ := exists_hom_equiv_Mod_evaluation_symm_app_eq R S.val A t,
  use (sigma.ι X ⟨S,t⟩).val.app (op S.val) w,
  rw [← comp_apply, ← nat_trans.comp_app],
  change (((sigma.ι X ⟨S,t⟩) ≫ sigma.desc f).val.app (op S.val)) w = _,
  erw colimit.ι_desc,
  exact hw,
end

instance CondensedMod_has_enough_projective : enough_projectives (CondensedMod R) :=
begin
  constructor,
  intros B,
  obtain ⟨X,hX,f,hf⟩ := CondensedMod_has_enough_projectives_aux R B,
  resetI,
  constructor,
  refine ⟨X,hX,f,hf⟩,
end
