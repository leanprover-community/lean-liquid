import for_mathlib.snake_lemma

namespace category_theory

namespace snake_lemma

open category_theory.limits

universes v u
variables {A : Type u} [category.{v} A] [abelian A]
  {F G : snake_diagram ⥤ A} (η : F ⟶ G)

namespace δ_natural_setup

@[reassoc]
lemma aux1 (hF : is_snake_input F) (hG : is_snake_input G) :
  η.app (0, 2) ≫ hG.to_kernel = hF.to_kernel ≫
  kernel.lift _ (kernel.ι _ ≫ η.app _) sorry := sorry

@[reassoc]
lemma aux2 (hF : is_snake_input F) (hG : is_snake_input G) :
  kernel.lift (G.map (snake_diagram.hom (1, 2) (2, 2) is_snake_input.to_kernel._proof_2))
    (kernel.ι (F.map (snake_diagram.hom (1, 2) (2, 2) is_snake_input.to_kernel._proof_2)) ≫
    η.app (1, 2)) sorry ≫ inv hG.cokernel_to_top_right_kernel_to_right_kernel =
  inv hF.cokernel_to_top_right_kernel_to_right_kernel ≫
    cokernel.desc _ (kernel.lift _ (kernel.ι _ ≫ η.app _) sorry ≫ cokernel.π _) sorry := sorry

@[reassoc]
lemma aux3 (hF : is_snake_input F) (hG : is_snake_input G) :
  kernel.lift hG.bottom_left_cokernel_to (kernel.ι hF.bottom_left_cokernel_to ≫
    cokernel.desc (F.map (snake_diagram.hom (1, 0) (2, 1)
    is_snake_input.bottom_left_cokernel_to._proof_2)) (η.app (2, 1) ≫
    cokernel.π (G.map (snake_diagram.hom (1, 0) (2, 1)
    is_snake_input.bottom_left_cokernel_to._proof_2))) sorry) sorry ≫
    inv hG.left_cokernel_to_kernel_bottom_left_cokernel_to =
  inv hF.left_cokernel_to_kernel_bottom_left_cokernel_to ≫
  cokernel.desc _ (η.app _ ≫ cokernel.π _) sorry := sorry

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
    cokernel.desc _ (η.app _ ≫ cokernel.π _) sorry) sorry,
  { sorry },
  rw ht, clear ht, clear t, dsimp [s], clear s,
  simp only [category.assoc], congr' 1,
  rw aux3_assoc η hF hG, congr' 1,
  dsimp [is_snake_input.cokernel_to],
  apply coequalizer.hom_ext,
  simp,
end

end snake_lemma

end category_theory
