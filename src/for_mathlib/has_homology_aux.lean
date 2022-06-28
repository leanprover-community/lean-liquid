import for_mathlib.has_homology
import for_mathlib.complex_extend

noncomputable theory

open category_theory category_theory.limits

open_locale zero_object

section

variables {𝓐 : Type*} [category 𝓐] [abelian 𝓐]
variables {ι : Type*} {c : complex_shape ι}
variables (C : homological_complex 𝓐 c)

def chain_complex_nat_has_homology_0
  (C : chain_complex 𝓐 ℕ) :
  has_homology (C.d 1 0) (0 : _ ⟶ 0) (C.homology 0) :=
{ w := comp_zero,
  π := sorry, --(kernel.map_iso _ _ (iso.refl _) _ _).hom ≫ homology.π' _ _ sorry,
  ι := homology.ι _ _ _ ≫ (cokernel.map_iso _ _ (C.X_prev_iso rfl) (iso.refl _) (by sorry; simp [← iso.inv_comp_eq])).hom,
  π_ι := sorry,
  ex_π := sorry,
  ι_ex := sorry,
  epi_π := sorry,
  mono_ι := sorry }

def homological_complex_has_homology (i j k : ι) (hij : c.rel i j) (hjk : c.rel j k) :
  has_homology (C.d i j) (C.d j k) (C.homology j) :=
{ w := homological_complex.d_comp_d _ _ _ _,
  π := (kernel.map_iso _ _ (iso.refl _) (C.X_next_iso hjk).symm (by sorry; simp [iso.comp_inv_eq])).hom ≫ homology.π' _ _ _,
  ι := homology.ι _ _ _ ≫ (cokernel.map_iso _ _ (C.X_prev_iso hij) (iso.refl _) (by sorry; simp [← iso.inv_comp_eq])).hom,
  π_ι := by { simp only [category.assoc, homology.π'_ι_assoc, kernel.map_iso_hom, iso.refl_hom, cokernel.map_iso_hom, cokernel.π_desc, category.id_comp, kernel.lift_ι_assoc, category.comp_id] },
  ex_π := by { rw has_homology.exact_iso_comp_snd_iff_exact_comp_iso_fst_iff, simp only [iso.symm_hom, iso.refl_hom, kernel.map_iso_hom], sorry },
  ι_ex := sorry,
  epi_π := epi_comp _ _,
  mono_ι := mono_comp _ _ }

abbreviation chain_complex_nat_has_homology {𝓐 : Type*} [category 𝓐] [abelian 𝓐]
  (C : chain_complex 𝓐 ℕ) (n : ℕ) :
  has_homology (C.d (n+1+1) (n+1)) (C.d (n+1) n) (C.homology (n+1)) :=
homological_complex_has_homology C (n+1+1) (n+1) n rfl rfl

abbreviation cochain_complex_int_has_homology {𝓐 : Type*} [category 𝓐] [abelian 𝓐]
  (C : cochain_complex 𝓐 ℤ) (n : ℤ) :
  has_homology (C.d n (n+1)) (C.d (n+1) (n+1+1)) (C.homology (n+1)) :=
homological_complex_has_homology C n (n+1) (n+1+1) rfl rfl

end

def homology_embed_iso {𝓐 : Type*} [category 𝓐] [abelian 𝓐]
  (C : chain_complex 𝓐 ℕ) : Π (n : ℕ),
  ((homological_complex.embed complex_shape.embedding.nat_down_int_up).obj C).homology (-n) ≅
  C.homology n
| 0 :=
begin
  refine has_homology.iso _ (chain_complex_nat_has_homology_0 C),
  let C' := (homological_complex.embed complex_shape.embedding.nat_down_int_up).obj C,
  exact cochain_complex_int_has_homology C' (-(1:ℕ):ℤ),
end
| 1 :=
begin
  refine has_homology.iso _ (chain_complex_nat_has_homology C 0),
  let C' := (homological_complex.embed complex_shape.embedding.nat_down_int_up).obj C,
  exact cochain_complex_int_has_homology C' (-(1+1:ℕ):ℤ),
end
| (n+1+1) :=
begin
  refine has_homology.iso _ (chain_complex_nat_has_homology C (n+1)),
  let C' := (homological_complex.embed complex_shape.embedding.nat_down_int_up).obj C,
  exact cochain_complex_int_has_homology C' (-(n+1+1+1:ℕ):ℤ),
end

def map_homological_complex_embed
  {𝓐 𝓑 : Type*} [category 𝓐] [abelian 𝓐] [category 𝓑] [abelian 𝓑]
  (F : 𝓐 ⥤ 𝓑) [F.additive] :
  (homological_complex.embed complex_shape.embedding.nat_down_int_up) ⋙
  F.map_homological_complex _ ≅
  F.map_homological_complex _ ⋙
  (homological_complex.embed complex_shape.embedding.nat_down_int_up) :=
nat_iso.of_components (λ C, homological_complex.hom.iso_of_components
  (λ n, by { rcases n with ((_|n)|n),
    { exact iso.refl _ },
    { apply functor.map_zero_object },
    { exact iso.refl _ }, })
  begin
    rintro i j (rfl : _ = _), rcases i with (n|(_|n)),
    { apply is_zero.eq_of_tgt, apply is_zero_zero, },
    { erw [category.id_comp, category.comp_id], refl, },
    { erw [category.id_comp, category.comp_id], refl, },
  end)
begin
  intros C₁ C₂ f, ext ((_|n)|n) : 2,
  { rw [homological_complex.comp_f, homological_complex.comp_f],
    dsimp, erw [category.id_comp, category.comp_id], refl, },
  { apply is_zero.eq_of_tgt, apply is_zero_zero, },
  { rw [homological_complex.comp_f, homological_complex.comp_f],
    dsimp, erw [category.id_comp, category.comp_id], refl, },
end
