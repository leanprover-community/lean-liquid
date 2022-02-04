import algebra.category.Module.abelian
import algebra.category.Module.adjunctions
import algebra.category.Module.filtered_colimits
import algebra.category.Module.colimits
import condensed.adjunctions

open category_theory
open category_theory.limits

universe u

variables (A : Type (u+1)) [ring A]

abbreviation CondensedMod := Condensed.{u} (Module.{u+1} A)

noncomputable theory

instance forget_Module_preserves_colimits_proetale_topology_cover (X : Profinite.{u}) :
  limits.preserves_colimits_of_shape (proetale_topology.cover X)ᵒᵖ
  (forget (Module.{u+1} A)) := infer_instance

-- TODO: Move this. Also, do we have this somewhere already?
instance forget_Module_reflects_isomorphisms :
  reflects_isomorphisms (forget (Module.{u+1} A)) :=
begin
  constructor,
  introsI M N f h,
  rw is_iso_iff_bijective at *,
  let e := linear_equiv.of_bijective f h.1 h.2,
  use e.symm,
  split,
  { ext t, change e.symm (e t) = t, rw linear_equiv.symm_apply_apply },
  { ext t, change e (e.symm t) = t, rw linear_equiv.apply_symm_apply }
end

-- (AT) I will fix this in mathlib asap...
instance : has_colimits (Module.{u+1} A) :=
Module.colimits.has_colimits_Module.{(u+1) (u+1)}

instance abelian_CondensedMod : abelian (CondensedMod A) :=
begin
  apply @category_theory.Sheaf.abelian.{(u+2) u (u+1)}
    Profinite.{u} _ proetale_topology (Module.{u+1} A) _ _ _ _ _ _ _ _,
end

def CondensedMod_to_CondensedSet : (CondensedMod A) ⥤ CondensedSet :=
Sheaf_compose _ (forget _)

@[simps obj_val map]
def CondensedSet_to_CondensedMod : CondensedSet ⥤ (CondensedMod A) :=
Sheaf.compose_and_sheafify _ (Module.free A)

@[simps unit_app counit_app]
def CondensedMod_CondensedSet_adjunction :
  CondensedSet_to_CondensedMod A ⊣ CondensedMod_to_CondensedSet A :=
Sheaf.adjunction _ (Module.adj A)

@[simp]
lemma CondensedMod_CondensedSet_adjunction_hom_equiv_apply (X : CondensedSet)
  (Y : CondensedMod A) (e : (CondensedSet_to_CondensedMod A).obj X ⟶ Y) :
  ((CondensedMod_CondensedSet_adjunction A).hom_equiv _ _ e).val =
  ((Module.adj A).whisker_right _).hom_equiv _ _ (proetale_topology.to_sheafify _ ≫ e.val) := rfl

@[simp]
lemma CondensedMod_CondensedSet_adjunction_hom_equiv_symm_apply (X : CondensedSet)
  (Y : CondensedMod A) (e : X ⟶ (CondensedMod_to_CondensedSet A).obj Y) :
  (((CondensedMod_CondensedSet_adjunction A).hom_equiv _ _).symm e).val =
  proetale_topology.sheafify_lift
    ((((Module.adj A).whisker_right _).hom_equiv _ _).symm e.val) Y.2 := rfl
