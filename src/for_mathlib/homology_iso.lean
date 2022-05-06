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

-- TODO: replace this with the defn below it
noncomputable
def homology_iso :
  (homology_functor A _ j).obj X ≅ homology _ _ (X.d_comp_d i j k) :=
{ hom := homology.desc' _ _ _ ((kernel_d_from_iso _ _ k hjk).hom ≫
    homology.π' _ _ _)
  begin
    rw [kernel_lift_comp_kernel_d_from_iso_hom_assoc _ _ _ _ hij hjk,
      kernel_lift_eq _ _ _ _ hij hjk],
    simp only [category.assoc, homology.condition_π', comp_zero],
  end,
  inv := homology.desc' _ _ _
    ((kernel_d_from_iso _ _ k hjk).inv ≫ homology.π' _ _ _)
  begin
    have := kernel_lift_comp_kernel_d_from_iso_hom X i j k hij hjk,
    rw [← iso.eq_comp_inv, kernel_lift_eq _ _ _ _ hij hjk, category.assoc,
      ← iso.inv_comp_eq] at this,
    rw [← category.assoc, ← this],
    simp only [category.assoc, homology.condition_π', comp_zero],
  end,
  hom_inv_id' := by { ext, simp only [category.assoc, kernel_d_from_iso_inv, kernel_d_from_iso_hom,
    homology.π'_desc'_assoc, homology.π'_ι, kernel.lift_ι_assoc, category.id_comp] },
  inv_hom_id' := by { ext, simp only [category.assoc, kernel_d_from_iso_hom, kernel_d_from_iso_inv,
    homology.π'_desc'_assoc, homology.π'_ι, kernel.lift_ι_assoc, category.id_comp]} }
.

noncomputable
def homology_iso' :
  (homology_functor A _ j).obj X ≅ homology _ _ (X.d_comp_d i j k) :=
begin
  refine homology.map_iso _ _ _ _ _,
  { refine arrow.iso_mk (X.X_prev_iso hij) (iso.refl _) _,
    dsimp, simp only [X.d_to_eq hij, category.comp_id], },
  { refine arrow.iso_mk (iso.refl _) (X.X_next_iso hjk) _,
    dsimp, simp only [X.d_from_comp_X_next_iso hjk, category.id_comp], },
  { refl }
end

noncomputable
def homology_iso_map {X Y : homological_complex A c} (f : X ⟶ Y) :
  (homology_functor A _ j).map f =
  (homology_iso' X _ _ _ hij hjk).hom ≫
  homology.map _ _ ⟨f.f i, f.f j, f.comm _ _⟩ ⟨f.f j, f.f k, f.comm _ _⟩ rfl ≫
  (homology_iso' Y _ _ _ hij hjk).inv :=
begin
  simp only [homology_functor_map, homology_iso', homological_complex.hom.sq_from_left,
    homology.map_iso, homology.map_comp],
  congr' 1; ext,
  { simp only [homological_complex.hom.sq_to_left, comma.comp_left, arrow.iso_mk_hom_left,
      arrow.iso_mk_inv_left, f.prev_eq hij], },
  { simp only [homological_complex.hom.sq_to_right, comma.comp_right, arrow.iso_mk_hom_right,
      iso.refl_hom, arrow.iso_mk_inv_right, iso.refl_inv, category.id_comp],
    erw [category.comp_id] },
  { simp only [homological_complex.hom.sq_from_left, comma.comp_left, arrow.iso_mk_hom_left,
      iso.refl_hom, arrow.iso_mk_inv_left, iso.refl_inv, category.id_comp],
    erw [category.comp_id] },
  { simp only [homological_complex.hom.sq_from_right, comma.comp_right, arrow.iso_mk_hom_right,
      arrow.iso_mk_inv_right, f.next_eq hjk], }
end

end category_theory
