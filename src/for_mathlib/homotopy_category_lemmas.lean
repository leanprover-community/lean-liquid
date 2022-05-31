import category_theory.abelian.homology
import algebra.homology.homotopy

open category_theory
open category_theory.limits

namespace homotopy

universes v u
variables {M : Type*} {c : complex_shape M}
  (A : Type u) [category.{v} A] [abelian A]

variables (C₁ C₂ : homological_complex A c) (f₁ f₂ : C₁ ⟶ C₂)

lemma kernel_ι_comp_comp_cokernel_π_of_homotopy (h : homotopy f₁ f₂) (i : M) :
  kernel.ι (C₁.d_from i) ≫ f₁.f i ≫ cokernel.π (C₂.d_to i) =
  kernel.ι _ ≫ f₂.f i ≫ cokernel.π _ :=
sorry

end homotopy
