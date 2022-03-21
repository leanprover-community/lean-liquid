import algebra.homology.homology
import category_theory.abelian.homology

namespace category_theory

open category_theory.limits

variables {A ι : Type*} [category A] [abelian A] {c : complex_shape ι}
  (X : homological_complex A c)

variables (i j k :  ι) (hij : c.rel i j)
  (hjk : c.rel j k)

section

include hjk

noncomputable theory

@[simps]
def kernel_d_from_iso :
  kernel (X.d_from j) ≅ kernel (X.d j k) :=
{ hom := kernel.lift _ (kernel.ι _) begin
    apply_fun (λ e, e ≫ (X.X_next_iso hjk).inv),
    swap,
    { intros u v h,
      apply_fun (λ e, e ≫ (X.X_next_iso hjk).hom) at h,
      simpa using h },
    dsimp,
    rw [category.assoc, ← X.d_from_eq hjk],
    simp,
  end,
  inv := kernel.lift _ (kernel.ι _) begin
    rw X.d_from_eq hjk,
    simp,
  end,
  hom_inv_id' := by { ext, simp },
  inv_hom_id' := by { ext, simp } }

include hij

@[reassoc]
lemma kernel_lift_comp_kernel_d_from_iso_hom :
  kernel.lift (X.d_from j) (X.d_to j) (by simp) ≫
  (kernel_d_from_iso X j k hjk).hom =
  kernel.lift _ (X.d_to _) (by simp [X.d_to_eq hij]) :=
by { ext, dsimp, simp }

lemma kernel_lift_eq :
  kernel.lift (X.d j k) (homological_complex.d_to X j)
    (by simp [X.d_to_eq hij]) =
  (X.X_prev_iso hij).hom ≫ kernel.lift _ _ (X.d_comp_d i j k) :=
begin
  ext,
  dsimp,
  simp [X.d_to_eq hij],
end

end

include hij hjk

noncomputable
def homology_iso :
(homology_functor A _ j).obj X ≅ homology _ _ (X.d_comp_d i j k) :=
{ hom := homology.desc' _ _ _ ((kernel_d_from_iso _ _ k hjk).hom ≫
    homology.π' _ _ _)
  begin
    rw kernel_lift_comp_kernel_d_from_iso_hom_assoc _ _ _ _ hij hjk,
    rw kernel_lift_eq _ _ _ _ hij hjk,
    simp,
  end,
  inv := homology.desc' _ _ _
    ((kernel_d_from_iso _ _ k hjk).inv ≫ homology.π' _ _ _)
  begin
    have := kernel_lift_comp_kernel_d_from_iso_hom X i j k hij hjk,
    rw ← iso.eq_comp_inv at this,
    rw ← category.assoc,
    rw kernel_lift_eq _ _ _ _ hij hjk at this,
    rw category.assoc at this,
    rw ← iso.inv_comp_eq at this,
    rw ← this,
    simp,
  end,
  hom_inv_id' := by { ext, simp },
  inv_hom_id' := by { ext, simp } }

end category_theory
