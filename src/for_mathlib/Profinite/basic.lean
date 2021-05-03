import category_theory.Fintype
import topology.category.Profinite

open category_theory

universe u

namespace Profinite

@[simp]
lemma id_to_fun {X : Profinite.{u}} : (𝟙 X : X → X) = id := rfl

@[simp]
lemma comp_to_fun {X Y Z : Profinite.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
  (f ≫ g : X → Z) = g ∘ f := rfl

lemma comp_apply {X Y Z : Profinite.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
  (f ≫ g) x = g (f x) := rfl

lemma id_apply {X : Profinite.{u}} (x : X) : (𝟙 X : X ⟶ X) x = x := rfl

/-
lemma hom_closed {X Y : Profinite.{u}} (f : X ⟶ Y) :
  is_closed_map f :=
begin
  intros C hC,
  apply is_compact.is_closed,
  apply is_compact.image _ f.continuous,
  apply is_closed.compact hC,
end

/-- A bijective morphism of profinite sets is an isomorphism. -/
noncomputable
def iso_of_bijective {X Y : Profinite.{u}} (f : X ⟶ Y)
  (h : function.bijective f) : X ≅ Y :=
let E  := equiv.of_bijective _ h,
    hE : continuous E.symm :=
begin
  rw continuous_iff_is_closed,
  intros C hC,
  convert ← hom_closed f C hC,
  erw equiv.image_eq_preimage E,
end in
{ hom := f,
  inv := ⟨E.symm, hE⟩,
  hom_inv_id' := begin
    ext1 x,
    change E.inv_fun (E.to_fun x) = x,
    rw E.left_inv,
  end,
  inv_hom_id' := begin
    ext1 x,
    change E.to_fun (E.inv_fun x) = x,
    rw E.right_inv,
  end }

lemma is_iso_of_bijective {X Y : Profinite.{u}}
  (f : X ⟶ Y) (h : function.bijective f) : is_iso f :=
let E := iso_of_bijective f h in
is_iso.mk $ ⟨E.inv, by erw E.hom_inv_id, by erw E.inv_hom_id⟩
-/

/-- Construct a homeomorphism from an isomorphism. -/
def homeo_of_iso {X Y : Profinite} (f : X ≅ Y) : X ≃ₜ Y :=
{ to_fun := f.hom,
  inv_fun := f.inv,
  left_inv := λ x, by {change (f.hom ≫ f.inv) x = x, simp},
  right_inv := λx, by {change (f.inv ≫ f.hom) x = x, simp},
  continuous_to_fun := f.hom.continuous,
  continuous_inv_fun := f.inv.continuous }

end Profinite
