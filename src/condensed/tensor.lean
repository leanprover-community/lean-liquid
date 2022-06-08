import condensed.adjunctions
import condensed.extr.equivalence
import linear_algebra.tensor_product

noncomputable theory

universes u

open category_theory

namespace ExtrSheafProd

open_locale tensor_product

def tensor_presheaf (M : ExtrDisc.{u}ᵒᵖ ⥤ Ab.{u+1}) (A : Ab.{u+1}) :
  ExtrDisc.{u}ᵒᵖ ⥤ Ab.{u+1} :=
{ obj := λ S, AddCommGroup.of $ M.obj S ⊗[ℤ] A,
  map := λ S T f, (tensor_product.map (M.map f).to_int_linear_map $
    linear_map.id).to_add_monoid_hom,
  map_id' := sorry,
  map_comp' := sorry }

def tensor (M : ExtrSheafProd.{u} Ab.{u+1}) (A : Ab.{u+1}) :
  ExtrSheafProd.{u} Ab.{u+1} :=
{ val := tensor_presheaf M.val A,
  cond := sorry } -- tensor product commutes with direct sums.

-- Slow, so probably break into pieces
/-- This is the functor that sends `A : Ab` to `M ⊗ A`,
where `M` is a fixed condensed abelian group. -/
def tensor_functor : ExtrSheafProd.{u} Ab.{u+1} ⥤ Ab.{u+1} ⥤ ExtrSheafProd.{u} Ab.{u+1} :=
{ obj := λ M,
  { obj := λ A, tensor M A,
    map := λ A B f,
      ⟨{ app := λ S, (tensor_product.map linear_map.id f.to_int_linear_map).to_add_monoid_hom,
         naturality' := sorry }⟩,
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
where `M` is a fixed condensed abelian group. -/
def tensor_functor : Condensed.{u} Ab.{u+1} ⥤ Ab.{u+1} ⥤ Condensed.{u} Ab.{u+1} :=
(Condensed_ExtrSheafProd_equiv Ab.{u+1}).functor ⋙
((whiskering_right _ _ _).obj $ ((whiskering_right _ _ _).obj
  (Condensed_ExtrSheafProd_equiv Ab.{u+1}).inverse)).obj
  ExtrSheafProd.tensor_functor

/-- This is the functor that sends `A : Ab` to `M ⊗ A`,
where `M` is a fixed condensed abelian group. -/
def tensor (M : Condensed.{u} Ab.{u+1}) (A : Ab.{u+1}) : Condensed.{u} Ab.{u+1} :=
(tensor_functor.obj M).obj A

def tensor_functor_conj_iso :
  (Condensed_ExtrSheafProd_equiv Ab.{u+1}).inverse ⋙
  ((whiskering_right _ _ _).obj $ ((whiskering_right _ _ _).obj
    (Condensed_ExtrSheafProd_equiv Ab.{u+1}).functor)).obj tensor_functor ≅
  ExtrSheafProd.tensor_functor :=
sorry

end condensed
