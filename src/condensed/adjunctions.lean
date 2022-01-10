import algebra.category.Group.adjunctions
import category_theory.sites.adjunction
import algebra.category.Group.abelian
import algebra.category.Group.filtered_colimits

import for_mathlib.SheafOfTypes_sheafification
import for_mathlib.whisker_adjunction
import for_mathlib.abelian_sheaves.main

import condensed.basic

universe u

open category_theory category_theory.limits

noncomputable theory

@[simps obj map]
def CondensedSet_to_presheaf : CondensedSet ⥤ Profiniteᵒᵖ ⥤ Type* :=
SheafOfTypes_to_presheaf _

@[simps obj_val map]
def presheaf_to_CondensedSet : (Profiniteᵒᵖ ⥤ Type*) ⥤ CondensedSet :=
presheaf_to_SheafOfTypes _

def CondensedSet_presheaf_adjunction : presheaf_to_CondensedSet ⊣ CondensedSet_to_presheaf :=
sheafification_adjunction_types _

@[simp]
lemma CondensedSet_presheaf_adjunction_hom_equiv_apply (X : Profiniteᵒᵖ ⥤ Type*)
  (Y : CondensedSet) (e : presheaf_to_CondensedSet.obj X ⟶ Y) :
  CondensedSet_presheaf_adjunction.hom_equiv _ _ e =
  proetale_topology.to_sheafify X ≫ e.val := rfl

@[simp]
lemma CondensedSet_presheaf_adjunction_hom_equiv_symm_apply (X : Profiniteᵒᵖ ⥤ Type*)
  (Y : CondensedSet) (e : X ⟶ CondensedSet_to_presheaf.obj Y) :
  ((CondensedSet_presheaf_adjunction.hom_equiv _ _).symm e).val =
  proetale_topology.sheafify_lift e (by { rw is_sheaf_iff_is_sheaf_of_type, exact Y.2 }) := rfl

@[simp]
lemma CondensedSet_presheaf_adjunction_unit_app (X : Profiniteᵒᵖ ⥤ Type*) :
  CondensedSet_presheaf_adjunction.unit.app X =
  proetale_topology.to_sheafify X := rfl

@[simp]
lemma CondensedSet_presheaf_adjunction_counit_app (Y : CondensedSet) :
  (CondensedSet_presheaf_adjunction.counit.app Y).val =
  proetale_topology.sheafify_lift (𝟙 _) (by { rw is_sheaf_iff_is_sheaf_of_type, exact Y.2 }) := rfl

-- I don't know why this is needed...
instance (X : Profinite.{u}): limits.preserves_colimits_of_shape (proetale_topology.cover X)ᵒᵖ
  (forget Ab.{u+1}) :=
preserves_filtered_colimits.preserves_filtered_colimits (proetale_topology.cover X)ᵒᵖ

instance : abelian (Condensed Ab.{u+1}) :=
begin
  -- I don't know why this is needed either...
  apply @category_theory.Sheaf.abelian.{(u+2) u (u+1)}
    Profinite.{u} _ proetale_topology Ab.{u+1} _ _ _ _ _ _ _ _,
end

@[simps obj_val map]
def Condensed_Ab_to_CondensedSet : Condensed Ab ⥤ CondensedSet :=
Sheaf_forget _

@[simps obj_val map]
def CondensedSet_to_Condensed_Ab : CondensedSet ⥤ Condensed Ab :=
Sheaf.compose_and_sheafify_from_types _ AddCommGroup.free

@[simps unit_app counit_app]
def Condensed_Ab_CondensedSet_adjunction :
  CondensedSet_to_Condensed_Ab ⊣ Condensed_Ab_to_CondensedSet :=
Sheaf.adjunction_to_types _ AddCommGroup.adj

@[simp]
lemma Condensed_Ab_CondensedSet_adjunction_hom_equiv_apply (X : CondensedSet)
  (Y : Condensed Ab) (e : CondensedSet_to_Condensed_Ab.obj X ⟶ Y) :
  (Condensed_Ab_CondensedSet_adjunction.hom_equiv _ _ e).val =
  (AddCommGroup.adj.whisker_right _).hom_equiv _ _ (proetale_topology.to_sheafify _ ≫ e.val) := rfl

@[simp]
lemma Condensed_Ab_CondensedSet_adjunction_hom_equiv_symm_apply (X : CondensedSet)
  (Y : Condensed Ab) (e : X ⟶ Condensed_Ab_to_CondensedSet.obj Y) :
  ((Condensed_Ab_CondensedSet_adjunction.hom_equiv _ _).symm e).val =
  proetale_topology.sheafify_lift
    (((AddCommGroup.adj.whisker_right _).hom_equiv _ _).symm e.val) Y.2 := rfl
