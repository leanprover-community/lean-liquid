import data.matrix.notation

import for_mathlib.snake_lemma
import for_mathlib.short_exact_sequence

noncomputable theory

open category_theory
open category_theory.limits

universes v u

namespace homological_complex

variables {C : Type u} [category.{v} C] [preadditive C]
variables [has_zero_object C] [has_equalizers C] [has_images C] [has_image_maps C] [has_cokernels C]
variables {ι : Type*} {c : complex_shape ι}

def mod_boundaries (A : homological_complex C c) (j : ι) : C :=
cokernel ((A.boundaries j).arrow)

def mod_boundaries_map {A B : homological_complex C c} (f : A ⟶ B) (j : ι) :
  A.mod_boundaries j ⟶ B.mod_boundaries j :=
cokernel.map _ _ (boundaries_map f j) (f.f j) $ by { rw image_subobject_map_arrow, refl }

@[simps]
def mod_boundaries_functor (j : ι) : homological_complex C c ⥤ C :=
{ obj := λ A, A.mod_boundaries j,
  map := λ A B f, mod_boundaries_map f j,
  map_id' := λ A,
  begin
    delta mod_boundaries mod_boundaries_map cokernel.map, ext,
    show cokernel.π (A.boundaries j).arrow ≫ _ = cokernel.π (A.boundaries j).arrow ≫ _,
    simp only [cokernel.π_desc, category.id_comp, id_f, category.comp_id],
  end,
  map_comp' := λ X Y Z f g,
  begin
    delta mod_boundaries mod_boundaries_map cokernel.map, ext,
    show cokernel.π (X.boundaries j).arrow ≫ _ = cokernel.π (X.boundaries j).arrow ≫ _,
    simp only [cokernel.π_desc, cokernel.π_desc_assoc, comp_f, category.assoc],
  end }
.

-- generalize to chain complexes over other shapes
@[simps]
def homology_to_mod_boundaries (n : ℕ) :
  homology_functor C (complex_shape.down ℕ) n ⟶ mod_boundaries_functor n :=
{ app := λ A, cokernel.map _ _ (𝟙 _) ((A.cycles n).arrow)
    (by simp only [boundaries_to_cycles_arrow, category.id_comp]),
  naturality' := λ A B f,
  begin
    ext,
    simp only [homology_functor_map, mod_boundaries_functor_map, homology.π_map_assoc],
    delta mod_boundaries_map homology.π cokernel.map cycles,
    simp only [cokernel.π_desc, cokernel.π_desc_assoc, comp_f, category.assoc,
      kernel_subobject_map_arrow_assoc, hom.sq_from_left],
  end }
.

-- generalize to chain complexes over other shapes
@[simps]
def mod_boundaries_to_cycles (n : ℕ) :
  mod_boundaries_functor (n+1) ⟶ cycles_functor C (complex_shape.down ℕ) n :=
{ app := λ A, factor_thru_kernel_subobject _
      (cokernel.desc _ (A.d _ _)
      begin
        rw [← boundaries_to_cycles_arrow, category.assoc],
        convert comp_zero,
        rw [cycles_eq_kernel_subobject, kernel_subobject_arrow_comp],
        simp only [complex_shape.down_rel],
      end)
    begin
      ext, show cokernel.π _ ≫ _ = cokernel.π _ ≫ _,
      rw [cokernel.π_desc_assoc, comp_zero],
      cases n,
      { simp only [comp_zero, chain_complex.next_nat_zero, d_from_eq_zero] },
      { rw [d_from_eq, d_comp_d_assoc, zero_comp], simp only [complex_shape.down_rel], },
    end,
  naturality' := λ A B f,
  begin
    ext, show cokernel.π _ ≫ _ = cokernel.π _ ≫ _,
    simp only [homology_functor_map, mod_boundaries_functor_map, homology.π_map_assoc],
    delta mod_boundaries_map homology.π cokernel.map,
    simp only [cokernel.π_desc, cokernel.π_desc_assoc, comp_f, category.assoc,
      kernel_subobject_map_arrow_assoc, hom.sq_from_left],
    simp only [cycles_functor_map, factor_thru_kernel_subobject_comp_arrow,
      cokernel.π_desc, hom.comm, cycles_map_arrow],
    delta cycles,
    simp only [cycles_functor_map, factor_thru_kernel_subobject_comp_arrow,
      cokernel.π_desc, hom.comm],
    simp only [← category.assoc], congr' 1,
    simp only [factor_thru_kernel_subobject_comp_arrow, cokernel.π_desc, category.assoc],
  end }
.

-- generalize to chain complexes over other shapes
@[simps]
def cycles_to_homology (n : ℕ) :
  cycles_functor C (complex_shape.down ℕ) n ⟶ homology_functor C (complex_shape.down ℕ) n :=
{ app := λ A, cokernel.π _,
  naturality' := λ A B f,
  begin
    simp only [cycles_functor_map, homology_functor_map],
    delta homology.map,
    rw cokernel.π_desc, refl,
  end }

variables (C)

abbreviation Fst : chain_complex (short_exact_sequence C) ℕ ⥤
  homological_complex C (complex_shape.down ℕ) :=
(short_exact_sequence.Fst C).map_homological_complex _

abbreviation Snd : chain_complex (short_exact_sequence C) ℕ ⥤
  homological_complex C (complex_shape.down ℕ) :=
(short_exact_sequence.Snd C).map_homological_complex _

abbreviation Trd : chain_complex (short_exact_sequence C) ℕ ⥤
  homological_complex C (complex_shape.down ℕ) :=
(short_exact_sequence.Trd C).map_homological_complex _

abbreviation Fst_Snd : Fst C ⟶ Snd C :=
nat_trans.map_homological_complex (short_exact_sequence.f_nat C) _

abbreviation Snd_Trd : Snd C ⟶ Trd C :=
nat_trans.map_homological_complex (short_exact_sequence.g_nat C) _

variables (A : chain_complex (short_exact_sequence C) ℕ)

def snake_diagram (n : ℕ) : chain_complex (short_exact_sequence C) ℕ → snake_diagram ⥤ C :=
snake_diagram.mk_functor''
  ![Fst C, Snd C, Trd C]
  ![homology_functor _ _ (n+1),
    mod_boundaries_functor (n+1),
    cycles_functor _ _ n,
    homology_functor _ _ n]
  (Fst_Snd C) (Snd_Trd C)
  (homology_to_mod_boundaries (n+1)) (mod_boundaries_to_cycles n) (cycles_to_homology n)

lemma snake_diagram_is_snake_input (n : ℕ) : is_snake_input (snake_diagram C n A) :=
sorry
-- { row_exact₁ := _,
--   row_exact₂ := _,
--   col_exact₁ := _,
--   col_exact₂ := _,
--   col_mono := _,
--   col_epi := _,
--   row_mono := _,
--   row_epi := _ }

def snake_input {C : Type*} [category C] [abelian C] (n : ℕ) :
  chain_complex (short_exact_sequence C) ℕ → snake_input C :=
λ A, ⟨snake_diagram C n A, snake_diagram_is_snake_input C A n⟩

def δ {C : Type*} [category C] [abelian C] (n : ℕ) (A : chain_complex (short_exact_sequence C) ℕ) :
  homology ((Trd C).obj A) (n+1) ⟶ homology ((Fst C).obj A) n :=
(snake_input n A).2.δ

lemma six_term_exact_seq {C : Type*} [category C] [abelian C]
  (n : ℕ) (A : chain_complex (short_exact_sequence C) ℕ) :
  exact_seq C [
    (homology_functor _ _ (n+1)).map ((Fst_Snd C).app A), -- Hⁿ⁺¹(A₁) ⟶ Hⁿ⁺¹(A₂)
    (homology_functor _ _ (n+1)).map ((Snd_Trd C).app A), -- Hⁿ⁺¹(A₂) ⟶ Hⁿ⁺¹(A₃)
    δ n A,                                                -- Hⁿ⁺¹(A₃) ⟶  Hⁿ(A₁)
    (homology_functor _ _ n).map ((Fst_Snd C).app A),     --  Hⁿ(A₁)  ⟶  Hⁿ(A₂)
    (homology_functor _ _ n).map ((Snd_Trd C).app A)      --  Hⁿ(A₁)  ⟶  Hⁿ(A₃)
  ] :=
begin
  have key := (snake_input n A).2.six_term_exact_seq,
  dsimp only [snake_input, snake_diagram,
    snake_diagram.mk_functor'', snake_diagram.mk_functor'] at key,
  refine exact_seq.congr key _, clear key,
  iterate 5 { refine exact_seq.arrow_congr.cons _ _, rotate },
  { apply exact_seq.arrow_congr.nil },
  { apply snake_diagram.mk_functor_map_f0 },
  { apply snake_diagram.mk_functor_map_g0 },
  { refl },
  { apply snake_diagram.mk_functor_map_f3 },
  { apply snake_diagram.mk_functor_map_g3 },
end

end homological_complex
