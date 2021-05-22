import algebra.homology.homological_complex
import category_theory.preadditive.additive_functor

namespace homological_complex

open category_theory category_theory.limits

variables {ι : Type} {V₁ V₂ : Type*} {c : complex_shape ι}
variables [category V₁] [category V₂] [preadditive V₁] [preadditive V₂]

-- this is of course functorial in `C`, see below
@[simps]
def modify (C : homological_complex V₁ c) (F : ι → V₁ ⥤ V₂) (α : Π i j, F i ⟶ F j)
  [Π i, (F i).additive] :
  homological_complex V₂ c :=
{ X := λ i, (F i).obj (C.X i),
  d := λ i j, (F i).map (C.d i j) ≫ (α i j).app _,
  shape' := λ i j h, by rw [C.shape _ _ h, category_theory.functor.map_zero, zero_comp],
  d_comp_d' := λ i j k hij hjk,
  by simp only [nat_trans.naturality_assoc, ← functor.map_comp_assoc, category.assoc, C.d_comp_d,
      category_theory.functor.map_zero, zero_comp, comp_zero], }

-- this is a generalization of `functor.map_homological_complex`
@[simps { fully_applied := ff }]
def modify_functor (F : ι → V₁ ⥤ V₂) (α : Π i j, F i ⟶ F j) [Π i, (F i).additive] :
  homological_complex V₁ c ⥤ homological_complex V₂ c :=
{ obj := λ C, C.modify F α,
  map := λ C₁ C₂ f,
  { f := λ i, (F i).map (f.f i),
    comm' :=
    begin
      intros i j hij, dsimp,
      rw [← category.assoc, ← (F i).map_comp, f.comm,
        (F i).map_comp, category.assoc, (α _ _).naturality, category.assoc],
    end },
  map_id' := by { intros X, dsimp at *, simp at *, refl },
  map_comp' := by { intros X Y Z f g, dsimp at *, simp at *, refl } }

end homological_complex
