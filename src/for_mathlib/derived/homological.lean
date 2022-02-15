import category_theory.triangulated.pretriangulated
import category_theory.abelian.exact
import category_theory.linear.yoneda
import algebra.category.Module.abelian
import category_theory.currying

namespace category_theory.triangulated

open category_theory
open category_theory.limits
open pretriangulated

universes v u
variables {C : Type u} [category.{v} C]
  [has_zero_object C]
  [preadditive C]
  [has_shift C ℤ]
  [∀ (n : ℤ), (shift_functor C n).additive]
  [pretriangulated C]

/-
A -> B -> C -> A[1]
then F(A) -> F(B) -> F(C) is exact.
-/
class homological_functor {A : Type*} [category A] [abelian A] (F : C ⥤ A) [F.additive] : Prop :=
(cond : ∀ (T : triangle C) (hT : T ∈ dist_triang C), exact (F.map T.mor₁) (F.map T.mor₂))

lemma complete_distinguished_triangle_morphism'
  (T₁ T₂ : triangle C)
  (h₁ : T₁ ∈ dist_triang C)
  (h₂ : T₂ ∈ dist_triang C)
  (f₂ : T₁.obj₂ ⟶ T₂.obj₂)
  (f₃ : T₁.obj₃ ⟶ T₂.obj₃)
  (w : T₁.mor₂ ≫ f₃ = f₂ ≫ T₂.mor₂) :
  ∃ f₁ : T₁.obj₁ ⟶ T₂.obj₁, (T₁.mor₁ ≫ f₂ = f₁ ≫ T₂.mor₁) ∧ (T₁.mor₃ ≫ f₁⟦1⟧' = f₃ ≫ T₂.mor₃) :=
begin
  let T₁' := T₁.rotate,
  let T₂' := T₂.rotate,
  obtain ⟨g,h1,h2⟩ := complete_distinguished_triangle_morphism T₁' T₂' _ _ f₂ f₃ w,
  use (shift_shift_neg _ _).inv ≫ g⟦(-1 : ℤ)⟧' ≫ (shift_shift_neg _ _).hom,
  split,
  { dsimp at h2,
    apply_fun (λ e, - (shift_functor C (-1 : ℤ)).map e ≫ (shift_shift_neg _ _).hom) at h2,
    simp only [category.assoc, functor.map_comp] at ⊢ h2,
    rw iso.eq_inv_comp,
    convert h2 using 1,
    { simp },
    { simp } },
  { convert h1 using 1,
    sorry },
  { rw ← rotate_distinguished_triangle, exact h₁ },
  { rw ← rotate_distinguished_triangle, exact h₂ }
end

theorem dist_triang_to_exact_complex
  (T : triangle C)
  (hT : T ∈ dist_triang C)
  (X : C)
  (f : X ⟶ T.obj₂)
  (hf : f ≫ T.mor₂ = 0) :
  ∃ g : X ⟶ T.obj₁, g ≫ T.mor₁ = f :=
begin
  let I : triangle C := contractible_triangle C X,
  obtain ⟨f₁,h₁,h₂⟩ :=
    complete_distinguished_triangle_morphism' I T
    (contractible_distinguished _) hT f 0
    (by simpa using hf.symm),
  use f₁,
  rw ← h₁,
  dsimp,
  simp,
end

variables {R : Type*} [ring R] [linear R C]

-- Move me
instance linear_yoneda_flip_additive (X : C) :
  ((linear_yoneda R C).flip.obj (opposite.op X)).additive := sorry

-- Prove this using the above theorem.
instance (X : C) : homological_functor ((linear_yoneda R C).flip.obj (opposite.op X)) :=
sorry

end category_theory.triangulated
