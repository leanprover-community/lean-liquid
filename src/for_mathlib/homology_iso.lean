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

variables {𝓐 : Type*} [category 𝓐] [abelian 𝓐]

open opposite

omit hij hjk

@[simps]
def homology_unop_iso {A B C : 𝓐ᵒᵖ} (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0) :
  homology f g w ≅ opposite.op (homology g.unop f.unop (by { rw [← unop_comp, w, unop_zero] })) :=
homology_iso_cokernel_lift _ _ _ ≪≫
  cokernel.map_iso _ (cokernel.desc g.unop f.unop _).op (iso.refl _) (cokernel_unop_op _).symm
    (by { apply quiver.hom.unop_inj, ext,
      simp only [unop_comp, iso.symm_hom, cokernel_unop_op_inv, quiver.hom.unop_op,
        cokernel.π_desc_assoc, iso.refl_hom, category.id_comp, cokernel.π_desc],
      rw [← unop_comp, kernel.lift_ι] }) ≪≫
  cokernel_op_op _ ≪≫
  (homology_iso_kernel_desc _ _ _).op

def homology_op_iso {A B C : 𝓐} (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0) :
  homology g.op f.op (by rw [← op_comp, w, op_zero]) ≅ opposite.op (homology f g w) :=
homology_unop_iso _ _ _

lemma homology_op_iso_eq_desc' {A B C : 𝓐} (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0) :
  (homology_op_iso f g w).hom =
  homology.desc' _ _ _ ((kernel_op_op f).hom ≫ (homology.ι _ _ _).op)
  begin
    rw ← category.assoc, let t := _, change t ≫ _ = _,
    have ht : t = (cokernel.desc _ g w).op,
    { dsimp [t],
      rw [← (kernel.lift f.op g.op _).op_unop, ← op_comp], congr' 1,
      apply coequalizer.hom_ext,
      simp only [cokernel.π_desc_assoc, cokernel.π_desc],
      rw [← unop_comp, kernel.lift_ι],
      refl },
    rw [ht, ← op_comp, homology.condition_ι], refl,
  end :=
begin
  apply homology.hom_from_ext,
  simp only [kernel_op_op_hom, homology.π'_desc'],
  dsimp [homology_op_iso, homology.π'],
  simp only [category.assoc, iso.inv_hom_id_assoc, cokernel.π_desc_assoc],
  refl,
end

attribute [reassoc] cokernel.map_desc

end category_theory
