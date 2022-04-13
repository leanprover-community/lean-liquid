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
instance : has_forget₂ SemiNormedGroup.{u} Ab.{u} :=
{ forget₂ :=
  { obj := λ V, AddCommGroup.of V,
    map := λ V W f, f.to_add_monoid_hom,
    map_id' := λ V, rfl,
    map_comp' := λ _ _ _ f g, rfl },
  forget_comp := rfl }

section LCC
-- maybe move this section

def LCC : Profinite.{u}ᵒᵖ ⥤ Ab.{u} :=
SemiNormedGroup.LCC.obj V ⋙ forget₂ _ _

def LCC_iso_Cond_of_top_ab :
  LCC.{u} V ≅ Condensed.of_top_ab.presheaf.{u} V :=
sorry

end LCC

lemma free_acyclic_aux (F : arrow Profinite) (hF : surjective (F.hom)) (i : ℕ) :
    is_zero ((((cosimplicial_object.augmented.whiskering Profiniteᵒᵖ Ab).obj
      (LCC V ⋙ Ab.ulift.{u+1})).obj F.augmented_cech_nerve.right_op).to_cocomplex.homology i) :=
begin
  sorry -- use `prop819` from `prop819.lean`,
end

theorem free_acyclic (i : ℤ) (hi : 0 < i) :
  is_zero (((Ext' i).obj (op ((Profinite_to_Condensed ⋙ CondensedSet_to_Condensed_Ab).obj S))).obj
    (Condensed.of_top_ab V)) :=
begin
  apply condensed.acyclic_of_exact _ _ _ i hi,
  intros F hF i,
  apply is_zero_of_iso_of_zero (free_acyclic_aux V F hF i),
  refine (homology_functor _ _ i).map_iso _,
  refine cosimplicial_object.augmented.cocomplex.map_iso _,
  conv_lhs { rw [← functor.flip_obj_obj] },
  conv_rhs { rw [← functor.flip_obj_obj] },
  refine functor.map_iso _ _,
  refine iso_whisker_right _ _,
  exact LCC_iso_Cond_of_top_ab V,
end

theorem free_pfpng_acyclic (i : ℤ) (hi : 0 < i) :
  is_zero (((Ext' i).obj (op ((condensify (free_pfpng_functor ⋙ to_CHFPNG₁)).obj S))).obj
    (Condensed.of_top_ab V)) :=
begin
  refine is_zero_of_iso_of_zero (free_acyclic S V i hi) _,
  conv { rw ← functor.flip_obj_obj, congr, skip, rw ← functor.flip_obj_obj },
  refine functor.map_iso _ (iso.app _ _).op,
  exact free_pfpng_profinite_iso
end
