import category_theory.preadditive.opposite
import algebra.homology.homological_complex

noncomputable theory

open opposite category_theory category_theory.limits

namespace homological_complex

variables {C : Type*} [category C] [preadditive C]
variables {ι : Type*} {c : complex_shape ι}

@[simps]
protected def op (X : homological_complex C c) : homological_complex Cᵒᵖ c.symm :=
{ X := λ i, op (X.X i),
  d := λ i j, (X.d j i).op,
  shape' := λ i j hij, by { rw [X.shape j i hij, op_zero], },
  d_comp_d' := by { intros, rw [← op_comp, X.d_comp_d, op_zero], } }

@[simps]
protected def unop (X : homological_complex Cᵒᵖ c) : homological_complex C c.symm :=
{ X := λ i, unop (X.X i),
  d := λ i j, (X.d j i).unop,
  shape' := λ i j hij, by { rw [X.shape j i hij, unop_zero], },
  d_comp_d' := by { intros, rw [← unop_comp, X.d_comp_d, unop_zero], } }

@[simps]
def op_functor : (homological_complex C c)ᵒᵖ ⥤ homological_complex Cᵒᵖ c.symm :=
{ obj := λ X, (unop X).op,
  map := λ X Y f,
  { f := λ i, (f.unop.f i).op,
    comm' := λ i j hij, by simp only [op_d, ← op_comp, f.unop.comm] }, }

@[simps]
def unop_functor : (homological_complex Cᵒᵖ c)ᵒᵖ ⥤ homological_complex C c.symm :=
{ obj := λ X, (unop X).unop,
  map := λ X Y f,
  { f := λ i, (f.unop.f i).unop,
    comm' := λ i j hij, by simp only [unop_d, ← unop_comp, f.unop.comm] }, }

end homological_complex
