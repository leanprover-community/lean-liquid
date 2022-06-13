import condensed.adjunctions
import condensed.extr.equivalence
import linear_algebra.tensor_product

import for_mathlib.endomorphisms.functor

noncomputable theory

universes u
open_locale tensor_product

open category_theory

namespace ExtrSheafProd

def tensor_presheaf (M : ExtrDisc.{u}ᵒᵖ ⥤ Ab.{u+1}) (A : Ab.{u+1}) :
  ExtrDisc.{u}ᵒᵖ ⥤ Ab.{u+1} :=
{ obj := λ S, AddCommGroup.of $ M.obj S ⊗[ℤ] A,
  map := λ S T f, (tensor_product.map (M.map f).to_int_linear_map $
    linear_map.id).to_add_monoid_hom,
  map_id' := λ X, by { ext x, apply tensor_product.induction_on x,
    { simp },
    { intros x y, dsimp, simp },
    { intros x y h1 h2,
      rw [add_monoid_hom.map_add, h1, h2], refl } },
  map_comp' := begin
    intros X Y Z f g,
    ext x,
    apply tensor_product.induction_on x,
    { simp },
    { intros x y, dsimp, simp },
    { intros x y h1 h2,
      rw [add_monoid_hom.map_add, add_monoid_hom.map_add, h1, h2] }
  end }

def tensor (M : ExtrSheafProd.{u} Ab.{u+1}) (A : Ab.{u+1}) :
  ExtrSheafProd.{u} Ab.{u+1} :=
{ val := tensor_presheaf M.val A,
  cond := sorry } -- tensor products commutes with direct sums.

-- Slow, so probably break into pieces
def tensor_functor : ExtrSheafProd.{u} Ab.{u+1} ⥤ Ab.{u+1} ⥤ ExtrSheafProd.{u} Ab.{u+1} :=
{ obj := λ M,
  { obj := λ A, tensor M A,
    map := λ A B f,
      ⟨{ app := λ S, (tensor_product.map linear_map.id f.to_int_linear_map).to_add_monoid_hom,
         naturality' := sorry
         }⟩,
    map_id' := sorry,
    map_comp' := sorry },
  map := λ M N f,
  { app := λ A,
    ⟨{ app := λ S, (tensor_product.map (f.val.app S).to_int_linear_map linear_map.id).to_add_monoid_hom,
       naturality' := sorry }⟩,
    naturality' := sorry },
  map_id' := sorry,
  map_comp' := sorry }

end ExtrSheafProd

namespace condensed

/-- This is the functor that sends `A : Ab` to `M ⊗ A`,
where `M` is a condensed abelian group, functorial in both `M` and `A`. -/
def tensor_functor : Condensed.{u} Ab.{u+1} ⥤ Ab.{u+1} ⥤ Condensed.{u} Ab.{u+1} :=
(Condensed_ExtrSheafProd_equiv Ab.{u+1}).functor ⋙
((whiskering_right _ _ _).obj $ ((whiskering_right _ _ _).obj
  (Condensed_ExtrSheafProd_equiv Ab.{u+1}).inverse)).obj
  ExtrSheafProd.tensor_functor

/-- This is the tensor product of a condensed abelian group `M` and `A : Ab`. -/
def tensor (M : Condensed.{u} Ab.{u+1}) (A : Ab.{u+1}) : Condensed.{u} Ab.{u+1} :=
(tensor_functor.obj M).obj A

/-- Restrincting to `ExtrDisc` works as expeceted. -/
def tensor_functor_conj_iso :
  (Condensed_ExtrSheafProd_equiv Ab.{u+1}).inverse ⋙
  ((whiskering_right _ _ _).obj $ ((whiskering_right _ _ _).obj
    (Condensed_ExtrSheafProd_equiv Ab.{u+1}).functor)).obj tensor_functor ≅
  ExtrSheafProd.tensor_functor :=
nat_iso.of_components
(λ X, begin
  refine functor.associator _ _ _ ≪≫ _,
  refine iso_whisker_left _ (Condensed_ExtrSheafProd_equiv Ab.{u+1}).counit_iso ≪≫ _,
  refine functor.right_unitor _ ≪≫ _,
  refine functor.map_iso _ _,
  exact ((Condensed_ExtrSheafProd_equiv Ab.{u+1}).counit_iso.app X),
end)
begin
  intros X Y f, ext : 2,
  dsimp [tensor_functor],
  simp only [equivalence.fun_inv_map, equivalence.equivalence_mk'_counit,
    equivalence.equivalence_mk'_counit_inv, functor.map_comp, nat_trans.comp_app,
    category.assoc, iso.inv_hom_id_app_assoc, category.id_comp,
    nat_iso.cancel_nat_iso_hom_left],
  rw [← nat_trans.comp_app, ← functor.map_comp, ← nat_trans.comp_app],
  have : (Condensed_ExtrSheafProd_equiv Ab).counit_iso.inv.app Y ≫
    (Condensed_ExtrSheafProd_equiv Ab).counit_iso.hom.app Y = 𝟙 _,
  { rw [← nat_trans.comp_app, iso.inv_hom_id], refl },
  rw this,
  simp only [nat_trans.comp_app],
  dsimp,
  simp only [category_theory.functor.map_id, nat_trans.id_app, category.comp_id],
end

def tensor_functor_conj_iso' :
  tensor_functor ⋙ (whiskering_right _ _ _).obj
  (Condensed_ExtrSheafProd_equiv _).functor ≅
  (Condensed_ExtrSheafProd_equiv _).functor ⋙ ExtrSheafProd.tensor_functor :=
nat_iso.of_components
(λ X, begin
  dsimp [tensor_functor],
  refine functor.associator _ _ _ ≪≫ _,
  refine _ ≪≫ functor.right_unitor _,
  refine ((whiskering_left _ _ _).obj _).map_iso _,
  refine (Condensed_ExtrSheafProd_equiv _).counit_iso,
end)
begin
  intros X Y f, ext : 2,
  dsimp [tensor_functor],
  simp, dsimp, simp,
end

/-- The tensor product behaves in the naive way when evaluated
on extremally disconnected sets. -/
def tensor_eval_iso
  (M : Condensed.{u} Ab.{u+1}) (A : Ab.{u+1}) (S : ExtrDisc.{u}) :
  (tensor M A).val.obj (opposite.op S.val) ≅
  AddCommGroup.of (M.val.obj (opposite.op S.val) ⊗[ℤ] A) :=
let e := (tensor_functor_conj_iso'.app M).app A,
  e' := (ExtrSheafProd_to_presheaf _).map_iso e in
e'.app (opposite.op S)

/-- A variant of the tensor product functor for the endormophism category. -/
def endo_tensor :
  (endomorphisms $ Condensed.{u} Ab.{u+1}) ⥤ Ab.{u+1} ⥤
  (endomorphisms $ Condensed.{u} Ab.{u+1}) :=
functor.flip $
{ obj := λ A, (tensor_functor.flip.obj A).map_endomorphisms,
  map := λ A B f, nat_trans.map_endomorphisms $ tensor_functor.flip.map f }

end condensed
