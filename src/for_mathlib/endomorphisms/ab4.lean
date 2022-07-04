import for_mathlib.endomorphisms.basic
import for_mathlib.ab4
import category_theory.limits.constructions.epi_mono

noncomputable theory

universes v u

open category_theory category_theory.limits

namespace category_theory

namespace endomorphisms

variables (𝓐 : Type u) [category.{v} 𝓐] [abelian 𝓐] [has_coproducts 𝓐] [AB4 𝓐]
  [has_products_of_shape (ulift.{v} ℕ) 𝓐]

instance : AB4 (endomorphisms 𝓐) :=
begin
  constructor, introsI α X Y f hf,
  let t := _, change mono t,
  suffices : mono ((endomorphisms.forget _).map t),
  { resetI, apply category_theory.reflects_mono (endomorphisms.forget _) },
  let e₁ : (endomorphisms.forget 𝓐).obj (∐ λ (a : α), X a) ≅
    ∐ (λ a : α, (endomorphisms.forget _).obj (X a)) :=
    preserves_colimit_iso _ _ ≪≫ has_colimit.iso_of_nat_iso (discrete.nat_iso $ λ _, iso.refl _),
  let e₂ : (endomorphisms.forget 𝓐).obj (∐ Y) ≅
    ∐ (λ a, (endomorphisms.forget _).obj (Y a)) :=
    preserves_colimit_iso _ _ ≪≫ has_colimit.iso_of_nat_iso (discrete.nat_iso $ λ _, iso.refl _),
  have : (endomorphisms.forget _).map t = e₁.hom ≫ _ ≫ e₂.inv,
  rotate 2,
  { apply sigma.desc,
    intros a,
    refine _ ≫ sigma.ι _ a,
    refine (endomorphisms.forget _).map (f a) },
  { dsimp [e₁, e₂, t],
    apply (is_colimit_of_preserves (endomorphisms.forget 𝓐) (colimit.is_colimit _)).hom_ext,
    intros j,
    dsimp,
    simp only [category.assoc],
    erw (is_colimit_of_preserves (endomorphisms.forget 𝓐) (colimit.is_colimit _)).fac_assoc,
    rw [← comp_f, colimit.ι_desc], dsimp, simp, dsimp, simp, apply_instance },
  rw this,
  apply_with mono_comp { instances := ff }, apply_instance,
  apply_with mono_comp { instances := ff }, swap, apply_instance,
  apply AB4.cond, intros a,
  apply category_theory.preserves_mono (endomorphisms.forget _),
end

end endomorphisms

end category_theory
