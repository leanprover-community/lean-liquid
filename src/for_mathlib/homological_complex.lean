import algebra.homology.additive

open category_theory

variables {V ι : Type*} {c : complex_shape ι} [category V] [limits.has_zero_morphisms V]
variables {C₁ C₂ C₃ : homological_complex V c}

namespace homological_complex

@[simps]
def iso_app (f : C₁ ≅ C₂) (i : ι) : C₁.X i ≅ C₂.X i :=
{ hom := f.hom.f i,
  inv := f.inv.f i,
  hom_inv_id' := by { erw [← comp_f, f.hom_inv_id, id_f] },
  inv_hom_id' := by { erw [← comp_f, f.inv_hom_id, id_f] } }

@[simps]
def iso_of_components (f : Π i, C₁.X i ≅ C₂.X i)
  (hf : ∀ i j, (f i).hom ≫ C₂.d i j = C₁.d i j ≫ (f j).hom) :
  C₁ ≅ C₂ :=
{ hom := { f := λ i, (f i).hom, comm' := hf },
  inv :=
  { f := λ i, (f i).inv,
    comm' := λ i j,
    calc (f i).inv ≫ C₁.d i j
        = (f i).inv ≫ (C₁.d i j ≫ (f j).hom) ≫ (f j).inv : by simp
    ... = (f i).inv ≫ ((f i).hom ≫ C₂.d i j) ≫ (f j).inv : by rw hf
    ... =  C₂.d i j ≫ (f j).inv : by simp },
  hom_inv_id' := by { ext i, exact (f i).hom_inv_id },
  inv_hom_id' := by { ext i, exact (f i).inv_hom_id } }

end homological_complex
