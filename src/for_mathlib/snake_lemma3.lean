import for_mathlib.snake_lemma2
import category_theory.abelian.homology
import for_mathlib.exact_seq2

noncomputable theory

open category_theory category_theory.limits

variables {𝒜 : Type*} [category 𝒜] [abelian 𝒜]

namespace category_theory

local notation `kernel_map`   := kernel.map _ _ _ _
local notation `cokernel_map` := cokernel.map _ _ _ _

namespace snake

lemma col_exact_aux (X : cochain_complex 𝒜 ℤ) : exact_seq 𝒜
[ (kernel.ι (homological_complex.d_to X 0))
, (kernel.lift (homological_complex.d_from X 0)
    (homological_complex.d_to X 0) (by simp))
, (homology.π' (homological_complex.d_to X 0)
    (homological_complex.d_from X 0) (by simp))] :=
begin
  apply exact_seq.cons,
  { rw abelian.exact_iff,
    refine ⟨by { ext, simp }, _⟩,
    have :
      kernel.ι (kernel.lift (homological_complex.d_from X 0) (homological_complex.d_to X 0) _) =
      kernel.lift _ (kernel.ι _) _ ≫ kernel.ι (homological_complex.d_to X 0),
    by { simp },
    rw this,
    simp only [category.assoc, cokernel.condition, comp_zero],
    have : homological_complex.d_to X 0 =
      kernel.lift (homological_complex.d_from X 0) (homological_complex.d_to X 0) (by simp) ≫
      kernel.ι _, by simp,
    slice_lhs 2 3 { rw this },
    rw kernel.condition_assoc,
    simp },
  { rw ← exact_iff_exact_seq,
    change exact _ (_ ≫ _),
    rw exact_comp_iso,
    apply abelian.exact_cokernel }
end

lemma row_exact₁_aux (X Y Z : cochain_complex 𝒜 ℤ)
  (f : X ⟶ Y)
  (g : Y ⟶ Z)
  [exact (f.f (-1)) (g.f (-1))]
  [exact (f.f 0) (g.f 0)]
  [exact (f.f 1) (g.f 1)]
  [epi (g.f (-1))]
  [epi (g.f 0)]
  [epi (g.f 1)]
  [mono (f.f (-1))]
  [mono (f.f 0)]
  [mono (f.f 1)] :
  exact (homological_complex.hom.prev f 0) (homological_complex.hom.prev g 0) :=
begin
  rw [f.prev_eq, g.prev_eq],
  rotate 2, exact (-1), swap, exact (-1), simp, swap, simp,
  simp,
  rw [← category.assoc, exact_comp_iso],
  apply category_theory.exact_comp_inv_hom_comp,
end

lemma row_exact₂_aux (X Y Z : cochain_complex 𝒜 ℤ)
  (f : X ⟶ Y)
  (g : Y ⟶ Z)
  [exact (f.f (-1)) (g.f (-1))]
  [exact (f.f 0) (g.f 0)]
  [exact (f.f 1) (g.f 1)]
  [epi (g.f (-1))]
  [epi (g.f 0)]
  [epi (g.f 1)]
  [mono (f.f (-1))]
  [mono (f.f 0)]
  [mono (f.f 1)] :
  exact
    (kernel.lift (homological_complex.d_from Y 0)
       (kernel.ι (homological_complex.d_from X 0) ≫ f.f 0)
       (by simp))
    (kernel.lift (homological_complex.d_from Z 0)
       (kernel.ι (homological_complex.d_from Y 0) ≫ g.f 0)
       (by simp)) :=
begin
  haveI : mono (homological_complex.hom.next f 0),
  { rw f.next_eq,
    rotate 2, exact 1, swap, simp,
    apply_with mono_comp { instances := ff },
    swap,
    apply_with mono_comp { instances := ff },
    all_goals { apply_instance } },
  haveI : exact (homological_complex.hom.next f 0) (homological_complex.hom.next g 0),
  { rw [f.next_eq, g.next_eq],
    rotate 2, exact 1, swap, exact 1, simp, swap, simp,
    simp,
    rw [← category.assoc, exact_comp_iso],
    apply category_theory.exact_comp_inv_hom_comp },
  let S := mk_of_sequence_hom
    (X.X 0)
    (Y.X 0)
    (Z.X 0)
    (X.X_next 0)
    (Y.X_next 0)
    (Z.X_next 0)
    (f.f 0) (g.f 0) (X.d_from 0) (Y.d_from 0) (Z.d_from 0)
    (f.next 0) (g.next 0) (by simp) (by simp),
  rw exact_iff_exact_seq,
  exact S.six_term_exact_seq.extract 0 2,
end

lemma mk_of_homology (X Y Z : cochain_complex 𝒜 ℤ)
  (f : X ⟶ Y) (g : Y ⟶ Z)
  [exact (f.f (-1)) (g.f (-1))]
  [exact (f.f 0) (g.f 0)]
  [exact (f.f 1) (g.f 1)]
  [epi (g.f (-1))]
  [epi (g.f 0)]
  [epi (g.f 1)]
  [mono (f.f (-1))]
  [mono (f.f 0)]
  [mono (f.f 1)] :
  snake
  -- the objects
         (kernel (X.d_to 0))             (kernel (Y.d_to 0))              (kernel (Z.d_to 0))
            (X.X_prev 0)                    (Y.X_prev 0)                     (Z.X_prev 0)
        (kernel (X.d_from 0))           (kernel (Y.d_from 0))            (kernel (Z.d_from 0))
  ((homology_functor _ _ 0).obj X) ((homology_functor _ _ 0).obj Y) ((homology_functor _ _ 0).obj Z)
  -- the maps
  (kernel.map _ _ (f.prev _) (f.f _) (by simp)) (kernel.map _ _ (g.prev _) (g.f _) (by simp))
  (kernel.ι _) (kernel.ι _) (kernel.ι _)
  (f.prev _) (g.prev _)
  (kernel.lift _ (X.d_to _) (by simp)) (kernel.lift _ (Y.d_to _) (by simp)) (kernel.lift _ (Z.d_to _) (by simp))
  (kernel.map _ _ (f.f _) (f.next _) (by simp)) (kernel.map _ _ (g.f _) (g.next _) (by simp))
  (homology.π' _ _ _) (homology.π' _ _ _) (homology.π' _ _ _)
  ((homology_functor _ _ _).map f) ((homology_functor _ _ _).map g) :=
{ row_exact₁ := row_exact₁_aux _ _ _ _ _,
  row_exact₂ := row_exact₂_aux _ _ _ _ _,
  row_epi := begin
    rw g.prev_eq,
    rotate 2, exact (-1),
    swap, simp,
    apply_with epi_comp { instances := ff },
    swap,
    apply_with epi_comp { instances := ff },
    all_goals { apply_instance }
  end,
  row_mono := infer_instance,
  col_exact_a := col_exact_aux _,
  col_exact_b := col_exact_aux _,
  col_exact_c := col_exact_aux _,
  col_mono_a := infer_instance,
  col_mono_b := infer_instance,
  col_mono_c := infer_instance,
  col_epi_a := epi_comp _ _,
  col_epi_b := epi_comp _ _,
  col_epi_c := epi_comp _ _,
  sq_a₀ := by simp,
  sq_b₀ := by simp,
  sq_a₁ := by { ext, simp },
  sq_b₁ := by { ext, simp },
  sq_a₂ := by simp,
  sq_b₂ := by simp }

end snake

end category_theory
