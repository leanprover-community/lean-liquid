import topology.category.Profinite.projective
import for_mathlib.Profinite.product

open category_theory

universe u

structure ExtrDisc :=
(val : Profinite.{u})
[cond : projective val]

namespace ExtrDisc

@[ext]
structure hom (X Y : ExtrDisc) :=
mk :: (val : X.val ⟶ Y.val)

@[simps]
instance : category ExtrDisc :=
{ hom := hom,
  id := λ X, ⟨𝟙 _⟩,
  comp := λ X Y Z f g, ⟨f.val ≫ g.val⟩ }

@[simps]
def _root_.ExtrDisc_to_Profinite : ExtrDisc ⥤ Profinite :=
{ obj := val,
  map := λ X Y f, f.val }

instance : concrete_category ExtrDisc :=
{ forget := ExtrDisc_to_Profinite ⋙ forget _,
  forget_faithful := ⟨⟩ }

instance (X : ExtrDisc) : projective X.val := X.cond

example (X : ExtrDisc) : projective (ExtrDisc_to_Profinite.obj X) :=
by { dsimp, apply_instance }

noncomputable
def split {X Y : ExtrDisc} (f : X ⟶ Y) (hf : function.surjective f.val) :
  Y ⟶ X :=
begin
  have : epi f.val, by rwa Profinite.epi_iff_surjective f.val,
  resetI,
  choose g h using projective.factors (𝟙 Y.val) f.val,
  exact ⟨g⟩,
end

@[simp]
lemma splitting_is_splitting {X Y : ExtrDisc} (f : X ⟶ Y)
  (hf : function.surjective f.val) : split f hf ≫ f = 𝟙 _ :=
begin
  have : epi f.val, by rwa Profinite.epi_iff_surjective f.val,
  resetI,
  ext1,
  exact (projective.factors (𝟙 Y.val) f.val).some_spec,
end

end ExtrDisc
