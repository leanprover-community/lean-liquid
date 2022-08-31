import for_mathlib.has_homology
import for_mathlib.complex_extend
import for_mathlib.homology_iso_datum

noncomputable theory

open category_theory category_theory.limits

open_locale zero_object

section

variables {𝓐 : Type*} [category 𝓐] [abelian 𝓐]
variables {ι : Type*} {c : complex_shape ι}
variables (C : homological_complex 𝓐 c)

def homological_complex_has_homology (i j k : ι) (hij : c.rel i j) (hjk : c.rel j k) :
  has_homology (C.d i j) (C.d j k) (C.homology j) :=
(homology_iso_datum.of_homological_complex C i j k hij hjk).has_homology

abbreviation chain_complex_nat_has_homology {𝓐 : Type*} [category 𝓐] [abelian 𝓐]
  (C : chain_complex 𝓐 ℕ) (n : ℕ) :
  has_homology (C.d (n+1+1) (n+1)) (C.d (n+1) n) (C.homology (n+1)) :=
homological_complex_has_homology C (n+1+1) (n+1) n rfl rfl

abbreviation cochain_complex_int_has_homology {𝓐 : Type*} [category 𝓐] [abelian 𝓐]
  (C : cochain_complex 𝓐 ℤ) (n : ℤ) :
  has_homology (C.d n (n+1)) (C.d (n+1) (n+1+1)) (C.homology (n+1)) :=
homological_complex_has_homology C n (n+1) (n+1+1) rfl rfl

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
    dsimp, erw [category.id_comp, category.comp_id], refl },
  { apply is_zero.eq_of_tgt, apply is_zero_zero, },
  { rw [homological_complex.comp_f, homological_complex.comp_f],
    dsimp, erw [category.id_comp, category.comp_id], },
end
