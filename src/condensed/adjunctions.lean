import condensed.ab
import for_mathlib.SheafOfTypes_sheafification
import for_mathlib.whisker_adjunction
import algebra.category.Group.adjunctions
import category_theory.sites.adjunction

open category_theory

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

/-
TODO: I think the automatically generated `unit_app` and `counit_app` need some adjusting...
It's hard to write down a good statement for these, precisely because there is no
separation between morphisms of sheaves and morphisms of underlying presheaves.

Namely:

This typechecks
example (X : CondensedSet) :
  CondensedSet_to_presheaf.map (Condensed_Ab_CondensedSet_adjunction.unit.app X) =
  (AddCommGroup.adj.whisker_right _).unit.app _ ≫
  whisker_right (proetale_topology.to_sheafify _) (forget Ab) := sorry

This does not
example (X : CondensedSet) :
  Condensed_Ab_CondensedSet_adjunction.unit.app X =
  (AddCommGroup.adj.whisker_right _).unit.app _ ≫
  whisker_right (proetale_topology.to_sheafify _) (forget Ab) := sorry
-/

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
