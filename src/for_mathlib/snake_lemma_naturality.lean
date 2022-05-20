import for_mathlib.snake_lemma

namespace category_theory

local notation x `⟶[`D`]` y := D.map (snake_diagram.hom x y)

namespace snake_lemma

open category_theory.limits

universes v u
variables {A : Type u} [category.{v} A] [abelian A]
  {F G : snake_diagram ⥤ A} (η : F ⟶ G)

namespace δ_natural_setup

@[reassoc]
lemma aux1 (hF : is_snake_input F) (hG : is_snake_input G) :
  η.app (0, 2) ≫ hG.to_kernel = hF.to_kernel ≫
  kernel.lift _ (kernel.ι _ ≫ η.app _) begin
    simp only [category.assoc, ← η.naturality, kernel.condition_assoc, zero_comp],
  end :=
begin
  apply equalizer.hom_ext,
  dsimp [is_snake_input.to_kernel],
  simp,
end

@[reassoc]
lemma aux2 (hF : is_snake_input F) (hG : is_snake_input G) :
  kernel.lift ((1, 2) ⟶[G] (2, 2)) (kernel.ι ((1, 2) ⟶[F] (2, 2)) ≫
    η.app (1, 2)) begin
      simp only [category.assoc, ← η.naturality, kernel.condition_assoc, zero_comp],
    end ≫ inv hG.cokernel_to_top_right_kernel_to_right_kernel =
  inv hF.cokernel_to_top_right_kernel_to_right_kernel ≫
    cokernel.desc _ (kernel.lift _ (kernel.ι _ ≫ η.app _) begin
      simp only [category.assoc, ← η.naturality, kernel.condition_assoc, zero_comp],
    end ≫ cokernel.π _) begin
      dsimp [is_snake_input.to_top_right_kernel],
      simp only [← category.assoc], let t := _, change t ≫ _ = _,
      have ht : t = η.app _ ≫ kernel.lift ((1,1) ⟶[G] (2,2)) ((1,0) ⟶[G] (1,1)) _,
      { apply equalizer.hom_ext, simp, },
      rw [ht, category.assoc, cokernel.condition, comp_zero],
    end :=
begin
  simp only [is_iso.eq_inv_comp, is_iso.comp_inv_eq, category.assoc],
  dsimp [is_snake_input.cokernel_to_top_right_kernel_to_right_kernel],
  apply equalizer.hom_ext,
  simp only [le_refl, and_true, category.assoc, nat_trans.naturality,
    kernel.condition_assoc, zero_comp, true_and,
    cokernel.condition, comp_zero, equalizer_as_kernel, kernel.lift_ι],
  apply coequalizer.hom_ext,
  simp only [category.assoc, nat_trans.naturality, cokernel.π_desc_assoc,
    kernel.lift_ι_assoc, kernel.lift_ι],
end

@[reassoc]
lemma aux3 (hF : is_snake_input F) (hG : is_snake_input G) :
  kernel.lift hG.bottom_left_cokernel_to (kernel.ι hF.bottom_left_cokernel_to ≫
    cokernel.desc ((1, 0) ⟶[F] (2, 1)) (η.app (2, 1) ≫
    cokernel.π ((1, 0) ⟶[G] (2, 1))) begin
      simp only [category.assoc, η.naturality_assoc, cokernel.condition, comp_zero],
    end) begin
      dsimp [is_snake_input.bottom_left_cokernel_to],
      simp only [category.assoc], let t := _, change _ ≫ t = _,
      have ht : t = cokernel.desc ((1,0) ⟶[F] (2,1)) ((2,1) ⟶[F] (2,2)) _ ≫ η.app _,
      { apply coequalizer.hom_ext, simp, },
      rw [ht, kernel.condition_assoc, zero_comp],
    end ≫
    inv hG.left_cokernel_to_kernel_bottom_left_cokernel_to =
  inv hF.left_cokernel_to_kernel_bottom_left_cokernel_to ≫
  cokernel.desc _ (η.app _ ≫ cokernel.π _) begin
    simp only [category.assoc, η.naturality_assoc, cokernel.condition, comp_zero],
  end :=
begin
  rw [is_iso.comp_inv_eq, category.assoc (inv _), is_iso.eq_inv_comp],
  dsimp [is_snake_input.left_cokernel_to_kernel_bottom_left_cokernel_to],
  apply coequalizer.hom_ext, apply equalizer.hom_ext,
  simp only [nat_trans.naturality_assoc, category.assoc, cokernel.π_desc_assoc,
    cokernel.π_desc, kernel.lift_ι, kernel.lift_ι_assoc],
end

end δ_natural_setup

open δ_natural_setup

theorem δ_natural (hF : is_snake_input F) (hG : is_snake_input G) :
  η.app (0,2) ≫ hG.δ = hF.δ ≫ η.app (3,0) :=
begin
  dsimp [is_snake_input.δ],
  simp only [category.assoc],
  rw aux1_assoc η hF hG,
  rw aux2_assoc η hF hG,
  simp_rw cancel_epi,
  apply coequalizer.hom_ext,
  dsimp [is_snake_input.δ_aux],
  simp only [cokernel.π_desc_assoc, category.assoc],
  simp only [← category.assoc], let t := _, change (t ≫ _) ≫ _ = _,
  let s := _, change _ = ((s ≫ _) ≫ _) ≫ _,
  have ht : t = s ≫ kernel.lift _ (kernel.ι _ ≫
    cokernel.desc _ (η.app _ ≫ cokernel.π _) begin
      simp only [category.assoc, η.naturality_assoc, cokernel.condition, comp_zero],
    end) _,
  rotate 2,
  { dsimp [is_snake_input.bottom_left_cokernel_to], simp only [category.assoc],
    let t := _, change _ ≫ t = _,
    have ht : t = cokernel.desc ((1,0) ⟶[F] (2,1)) ((2,1) ⟶[F] (2,2)) _ ≫ η.app _,
    { apply coequalizer.hom_ext, dsimp, simp, },
    rw [ht, kernel.condition_assoc, zero_comp] },
  { dsimp [t, s],
    apply equalizer.hom_ext,
    simp },
  rw ht, clear ht, clear t, dsimp [s], clear s,
  simp only [category.assoc], congr' 1,
  rw aux3_assoc η hF hG, congr' 1,
  dsimp [is_snake_input.cokernel_to],
  apply coequalizer.hom_ext,
  simp,
end

end snake_lemma

end category_theory
