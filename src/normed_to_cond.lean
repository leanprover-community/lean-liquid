import free_pfpng.main
import condensed.acyclic
import prop819
.

noncomputable theory

universes u

open category_theory opposite ProFiltPseuNormGrp₁
open function (surjective)
open_locale nnreal

variables (S : Profinite.{u})
variables (V : SemiNormedGroup.{u}) [complete_space V]

set_option pp.universes true

-- move me
instance SemiNormedGroup.forget₂ : has_forget₂ SemiNormedGroup.{u} Ab.{u} :=
{ forget₂ :=
  { obj := λ V, AddCommGroup.of V,
    map := λ V W f, f.to_add_monoid_hom,
    map_id' := λ V, rfl,
    map_comp' := λ _ _ _ f g, rfl },
  forget_comp := rfl }

-- move me
instance SemiNormedGroup.forget₂_additive :
  (forget₂ SemiNormedGroup.{u} Ab.{u}).additive :=
{ map_add' := by { intros, refl } }

section LCC
-- maybe move this section

def LCC : Profinite.{u}ᵒᵖ ⥤ Ab.{u} :=
SemiNormedGroup.LCC.obj V ⋙ forget₂ _ _

local attribute [instance] locally_constant.semi_normed_group locally_constant.pseudo_metric_space

open uniform_space

/-
TODO:
- endow `C(S, V)` with the sup norm, otherwise the `sorry`s below will be hard
-/

def LCC_iso_Cond_of_top_ab_fun :
  completion (locally_constant S V) → C(S, V) :=
completion.extension $ locally_constant.to_continuous_map

def LCC_iso_Cond_of_top_ab_equiv :
  completion (locally_constant S V) ≃ C(S, V) :=
equiv.of_bijective (LCC_iso_Cond_of_top_ab_fun S V)
begin
  split,
  { have := @locally_constant.to_continuous_map_injective S V _ _,
    sorry },
  { sorry }
end


def LCC_iso_Cond_of_top_ab_obj :
  completion (locally_constant S V) ≃+ C(S, V) :=
{ map_add' := λ f g, begin
    sorry
  end,
  .. LCC_iso_Cond_of_top_ab_equiv S V }

lemma LCC_iso_Cond_of_top_ab_natural {S T : Profinite.{u}} (f : S ⟶ T) :
  LCC_iso_Cond_of_top_ab_obj S V ∘
  completion.map (locally_constant.comap f) =
  (Condensed.of_top_ab.presheaf.{u} V).map f.op ∘
  LCC_iso_Cond_of_top_ab_obj T V :=
begin
  dsimp [LCC_iso_Cond_of_top_ab_obj, LCC_iso_Cond_of_top_ab_equiv, LCC_iso_Cond_of_top_ab_fun,
    equiv.of_bijective],
  -- apply completion.ext,
  -- rw completion.extension_map,
  sorry
end

def LCC_iso_Cond_of_top_ab :
  LCC.{u} V ≅ Condensed.of_top_ab.presheaf.{u} V :=
nat_iso.of_components
  (λ S, add_equiv.to_AddCommGroup_iso $ LCC_iso_Cond_of_top_ab_obj _ _)
  begin
    intros S T f,
    ext1 φ,
    have := LCC_iso_Cond_of_top_ab_natural V f.unop,
    convert congr_fun this φ using 1,
    clear this,
    delta LCC SemiNormedGroup.LCC,
    simp only [add_equiv.to_AddCommGroup_iso_hom, category_theory.comp_apply,
      add_equiv.coe_to_add_monoid_hom, add_equiv.apply_eq_iff_eq,
      functor.comp_map, curry.obj_obj_map, uncurry.obj_map,
      category_theory.functor.map_id, nat_trans.id_app,
      SemiNormedGroup.LocallyConstant_obj_map,
      SemiNormedGroup.Completion_map],
    erw [category.id_comp],
    refl,
  end

end LCC
