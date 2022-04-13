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

def LCC_iso_Cond_of_top_ab_obj (S) :
  (LCC.{u} V).obj S ≅ (Condensed.of_top_ab.presheaf.{u} V).obj S :=
sorry

def LCC_iso_Cond_of_top_ab :
  LCC.{u} V ≅ Condensed.of_top_ab.presheaf.{u} V :=
nat_iso.of_components
  (LCC_iso_Cond_of_top_ab_obj V) sorry

end LCC

