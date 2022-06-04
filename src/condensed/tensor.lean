import condensed.adjunctions
import condensed.extr.equivalence
import linear_algebra.tensor_product

noncomputable theory

universes u

open category_theory

namespace condensed

open_locale tensor_product

def tensor_ExtrSheafProd_presheaf (M : ExtrDisc.{u}ᵒᵖ ⥤ Ab.{u+1}) (A : Ab.{u+1}) :
  ExtrDisc.{u}ᵒᵖ ⥤ Ab.{u+1} :=
{ obj := λ S, AddCommGroup.of $ M.obj S ⊗[ℤ] A,
  map := λ S T f, (tensor_product.map (M.map f).to_int_linear_map $
    linear_map.id).to_add_monoid_hom,
  map_id' := sorry,
  map_comp' := sorry }

def tensor_ExtrSheafProd (M : ExtrSheafProd.{u} Ab.{u+1}) (A : Ab.{u+1}) :
  ExtrSheafProd.{u} Ab.{u+1} :=
{ val := tensor_ExtrSheafProd_presheaf M.val A,
  cond := sorry } -- tensor product commutes with direct sums.

/-- This is the functor that sends `A : Ab` to `M ⊗ A`,
where `M` is a fixed condensed abelian group. -/
def tensor (M : Condensed.{u} Ab.{u+1}) : Ab.{u+1} ⥤ Condensed.{u} Ab.{u+1} :=
sorry

end condensed
