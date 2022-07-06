import for_mathlib.homological_complex_op
import for_mathlib.homotopy_category

noncomputable theory

open opposite category_theory category_theory.limits

variables {ι : Type*} (c : complex_shape ι)

namespace complex_shape

@[simp]
lemma symm_next (i : ι) : c.symm.next i = c.prev i := rfl

@[simp]
lemma symm_prev (i : ι) : c.symm.prev i = c.next i := rfl

end complex_shape

namespace homological_complex

lemma op_functor_map_homotopy {ι C : Type*} {c : complex_shape ι} [category C] [preadditive C]
  {X Y : homological_complex C c}
  (f₁ f₂ : X ⟶ Y) (H : homotopy f₁ f₂) :
  homotopy
    (homological_complex.op_functor.map f₁.op)
    (homological_complex.op_functor.map f₂.op) :=
{ hom := λ i j, (H.hom j i).op,
  zero' := λ i j hij, by rw [H.zero j i hij, op_zero],
  comm := λ i, begin
    simp only [homological_complex.op_functor_map_f, quiver.hom.unop_op, H.comm i,
      op_add, add_left_inj],
    conv_lhs { rw add_comm, },
    congr' 1,
    { rcases hi : c.prev i with _ | ⟨j, hj⟩,
      { dsimp [prev_d, d_next],
        simpa only [hi], },
      { have hj' : c.symm.rel i j := hj,
        simpa only [prev_d_eq _ hj, d_next_eq _ hj'], }, },
    { rcases hi : c.next i with _ | ⟨j, hj⟩,
      { dsimp [prev_d, d_next],
        simpa only [hi], },
      { have hj' : c.symm.rel j i := hj,
        simpa only [d_next_eq _ hj, prev_d_eq _ hj'], }, },
  end, }

end homological_complex

namespace homotopy_category

variables {C : Type*} [category C] [preadditive C] {c}

def op_functor : (homotopy_category C c)ᵒᵖ ⥤ homotopy_category Cᵒᵖ c.symm :=
functor.left_op (category_theory.quotient.lift _
  (homological_complex.op_functor ⋙ homotopy_category.quotient Cᵒᵖ c.symm).right_op
(λ X Y f₁ f₂ h, begin
  dsimp only [functor.right_op],
  congr' 1,
  dsimp only [functor.comp_map],
  erw quotient.functor_map_eq_iff,
  refine ⟨homological_complex.op_functor_map_homotopy f₁ f₂ h.some⟩,
end))

def quotient_op_functor :
  (quotient C c).op ⋙ op_functor ≅ homological_complex.op_functor ⋙ quotient Cᵒᵖ c.symm :=
nat_iso.of_components (λ X, eq_to_iso (by refl))
(λ X Y f, by { dsimp, simpa only [category.comp_id, category.id_comp], })

def unop_functor : (homotopy_category Cᵒᵖ c)ᵒᵖ ⥤ homotopy_category C c.symm :=
functor.left_op (category_theory.quotient.lift _
  (homological_complex.unop_functor ⋙ homotopy_category.quotient C c.symm).right_op
(λ X Y f₁ f₂ h, begin
  dsimp only [functor.right_op],
  congr' 1,
  dsimp only [functor.comp_map],
  erw quotient.functor_map_eq_iff,
  let H := h.some,
  exact nonempty.intro
  { hom := λ i j, (H.hom j i).unop,
    zero' := λ i j hij, by rw [H.zero j i hij, unop_zero],
    comm := λ i, begin
      apply quiver.hom.op_inj,
      simp only [homological_complex.unop_functor_map_f, op_add, quiver.hom.op_unop,
        quiver.hom.unop_op, H.comm i],
      conv_lhs { congr, rw add_comm, },
      congr' 2,
      { rcases hi : c.prev i with _ | ⟨j, hj⟩,
        { dsimp [prev_d, d_next],
          simpa only [hi], },
        { have hj' : c.symm.rel i j := hj,
          simpa only [prev_d_eq _ hj, d_next_eq _ hj'], }, },
      { rcases hi : c.next i with _ | ⟨j, hj⟩,
        { dsimp [prev_d, d_next],
          simpa only [hi], },
        { have hj' : c.symm.rel j i := hj,
          simpa only [d_next_eq _ hj, prev_d_eq _ hj'], }, },
    end, },
end))

def quotient_unop_functor :
  (quotient Cᵒᵖ c).op ⋙ unop_functor ≅ homological_complex.unop_functor ⋙ quotient C c.symm :=
nat_iso.of_components (λ X, eq_to_iso (by refl))
(λ X Y f, by { dsimp, simpa only [category.comp_id, category.id_comp], })

end homotopy_category
