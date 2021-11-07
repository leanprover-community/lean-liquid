import category_theory.sites.sheaf

namespace category_theory.presheaf

open category_theory
open category_theory.limits
open opposite

universes v₁ v₂ u₁ u₂
variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]
  {J : grothendieck_topology C} (P : Cᵒᵖ ⥤ D)

noncomputable theory

def glue (hP : is_sheaf J P) (X : C) (E : D) (S : sieve X) (hS : S ∈ J X)
  (x : presieve.family_of_elements (P ⋙ coyoneda.obj (op E)) S)
  (hx : x.compatible) : E ⟶ P.obj (op X) :=
(hP E S hS x hx).some

@[simp]
lemma res_glue (hP : is_sheaf J P) (X : C) (E : D) (S : sieve X) (hS : S ∈ J X)
  (x : presieve.family_of_elements (P ⋙ coyoneda.obj (op E)) S)
  (hx : x.compatible) (Y : C) (f : Y ⟶ X) (hf : S f) :
  glue P hP X E S hS x hx ≫ P.map f.op  = x f hf :=
(hP E S hS x hx).some_spec.1 _ _

lemma glue_ext (hP : is_sheaf J P) (X : C) (E : D) (S : sieve X) (hS : S ∈ J X)
  (a b : E ⟶ P.obj (op X))
  (h : ∀ ⦃Y⦄ (f : Y ⟶ X) (hf : S f), a ≫ P.map f.op = b ≫ P.map f.op) :
  a = b :=
begin
  let x : presieve.family_of_elements (P ⋙ coyoneda.obj (op E)) S :=
    λ Y f hf, a ≫ P.map f.op,
  have hx : x.compatible,
  { intros Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w,
    dsimp [x],
    simp only [category.assoc, ← P.map_comp, ← op_comp, w] },
  have : a = glue P hP X E S hS x hx,
  { apply (hP E S hS x hx).some_spec.2,
    tidy },
  rw this,
  symmetry,
  apply (hP E S hS x hx).some_spec.2,
  tidy,
end

end category_theory.presheaf
