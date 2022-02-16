import category_theory.derived
import data.matrix.notation

import for_mathlib.homological_complex
import for_mathlib.horseshoe
import for_mathlib.split_exact

noncomputable theory

open category_theory
open category_theory.limits
open short_exact_sequence

universes v u

namespace category_theory

variables {C : Type u} [category.{v} C] {D : Type*} [category D]

-- Importing `category_theory.abelian.projective` and assuming
-- `[abelian C] [enough_projectives C] [abelian D]` suffices to acquire all the following:
-- variables [preadditive C] [has_zero_object C] [has_equalizers C]
-- variables [has_images C] [has_projective_resolutions C]
-- variables [preadditive D] [has_zero_object D] [has_equalizers D] [has_cokernels D]
-- variables [has_images D] [has_image_maps D]

variables [abelian C] [enough_projectives C] [abelian D]

namespace functor
namespace left_derived

variables (F : C ⥤ D)

/-- We can compute a left derived functor using a chosen projective resolution. -/
@[simps]
def functor.left_derived_obj_iso' (F : C ⥤ D) [F.additive] (n : ℕ)
  (X : C) (P : chain_complex C ℕ) (π : P ⟶ ((chain_complex.single₀ C).obj X))
  (h : P.is_projective_resolution X π) :
  (F.left_derived n).obj X ≅
    (homology_functor D _ n).obj ((F.map_homological_complex _).obj P) :=
(F.left_derived_obj_iso n (h.mk_ProjectiveResolution P X π) : _)

/-- We can compute a left derived functor on a morphism using a lift of that morphism to a chain map
between chosen projective resolutions. -/
lemma functor.left_derived_map_eq' (F : C ⥤ D) [F.additive] (n : ℕ) (X Y : C) (f : X ⟶ Y)
  (PX : chain_complex C ℕ) (πX : PX ⟶ ((chain_complex.single₀ C).obj X))
  (PY : chain_complex C ℕ) (πY : PY ⟶ ((chain_complex.single₀ C).obj Y)) (g : PX ⟶ PY)
  (hX : PX.is_projective_resolution X πX) (hY : PY.is_projective_resolution Y πY)
  (w : g ≫ πY = πX ≫ (chain_complex.single₀ C).map f) :
  (F.left_derived n).map f =
  (functor.left_derived_obj_iso' F n X PX πX hX).hom ≫
    (homology_functor D _ n).map ((F.map_homological_complex _).map g) ≫
    (functor.left_derived_obj_iso' F n Y PY πY hY).inv :=
begin
  let PXr := (hX.mk_ProjectiveResolution PX X πX),
  let PYr := (hY.mk_ProjectiveResolution PY Y πY),
  let gr : PXr.complex ⟶ PYr.complex := g,
  simpa using functor.left_derived_map_eq F n f gr w,
end
.

def δ [F.additive] (n : ℕ) (A : short_exact_sequence C) :
  (F.left_derived (n+1)).obj A.3 ⟶ (F.left_derived n).obj A.1 :=
begin
  let f₃ := functor.left_derived_obj_iso' F (n+1) _ _ _ (horseshoe_is_projective_resolution₃ A),
  let f₁ := functor.left_derived_obj_iso' F n _ _ _ (horseshoe_is_projective_resolution₁ A),
  refine f₃.hom ≫ _ ≫ f₁.symm.hom,
  apply homological_complex.δ n (map_complex_short_exact_sequence_of_split C F _
    (λ i, horseshoe_split A i)),
end

lemma exact_of_short_exact [F.additive] (n : ℕ) (A : short_exact_sequence C) :
  exact ((F.left_derived n).map A.f) ((F.left_derived n).map A.g) :=
begin
  let P := map_complex_short_exact_sequence_of_split C F _ (λ i, horseshoe_split A i),
  have := ((homological_complex.six_term_exact_seq n P).drop 3).pair,
  have H₁₂ := functor.left_derived_map_eq' F n A.1 A.2 A.f
    ((homological_complex.Fst C).obj (horseshoe A)) (horseshoe_to_single₁ A)
    ((homological_complex.Snd C).obj (horseshoe A)) (horseshoe_to_single₂ A)
    ((homological_complex.Fst_Snd C).app (horseshoe A))
    (horseshoe_is_projective_resolution₁ A)
    (horseshoe_is_projective_resolution₂ A) _,
  have H₂₃ := functor.left_derived_map_eq' F n A.2 A.3 A.g
    ((homological_complex.Snd C).obj (horseshoe A)) (horseshoe_to_single₂ A)
    ((homological_complex.Trd C).obj (horseshoe A)) (horseshoe_to_single₃ A)
    ((homological_complex.Snd_Trd C).app (horseshoe A))
    (horseshoe_is_projective_resolution₂ A)
    (horseshoe_is_projective_resolution₃ A) _,
  refine preadditive.exact_of_iso_of_exact' _ _ _ _ _ _ _ _ _ this,
  { let := functor.left_derived_obj_iso' F n A.1
      ((homological_complex.Fst C).obj (horseshoe A)) (horseshoe_to_single₁ A)
      (horseshoe_is_projective_resolution₁ A),
    exact this.symm },
  { let := functor.left_derived_obj_iso' F n A.2
      ((homological_complex.Snd C).obj (horseshoe A)) (horseshoe_to_single₂ A)
      (horseshoe_is_projective_resolution₂ A),
    exact this.symm },
  { let := functor.left_derived_obj_iso' F n A.3
      ((homological_complex.Trd C).obj (horseshoe A)) (horseshoe_to_single₃ A)
      (horseshoe_is_projective_resolution₃ A),
    exact this.symm },
  { rw [H₁₂, ← category.assoc, iso.symm_hom, iso.inv_hom_id, category.id_comp],
    simpa },
  { rw [H₂₃, ← category.assoc, iso.symm_hom, iso.inv_hom_id, category.id_comp],
    simpa },
  { ext i,
    apply horseshoe_g_comp_to_single₃_f, },
  { ext i,
    apply horseshoe_f_comp_to_single₂_f }
end

lemma exact_of_short_exact.δ_right [F.additive] (n : ℕ) (A : short_exact_sequence C) :
  exact ((F.left_derived (n + 1)).map A.g) (δ F n A) :=
begin
  let P := map_complex_short_exact_sequence_of_split C F _ (λ i, horseshoe_split A i),
  have := ((homological_complex.six_term_exact_seq n P).drop 1).pair,
  have H₂₃ := functor.left_derived_map_eq' F (n+1) A.2 A.3 A.g
    ((homological_complex.Snd C).obj (horseshoe A)) (horseshoe_to_single₂ A)
    ((homological_complex.Trd C).obj (horseshoe A)) (horseshoe_to_single₃ A)
    ((homological_complex.Snd_Trd C).app (horseshoe A))
    (horseshoe_is_projective_resolution₂ A)
    (horseshoe_is_projective_resolution₃ A) _,
  refine preadditive.exact_of_iso_of_exact' _ _ _ _ _ _ _ _ _ this,
  { let := functor.left_derived_obj_iso' F (n+1) A.2
      ((homological_complex.Snd C).obj (horseshoe A)) (horseshoe_to_single₂ A)
      (horseshoe_is_projective_resolution₂ A),
    exact this.symm },
  { let := functor.left_derived_obj_iso' F (n+1) A.3
      ((homological_complex.Trd C).obj (horseshoe A)) (horseshoe_to_single₃ A)
      (horseshoe_is_projective_resolution₃ A),
    exact this.symm },
  { let := functor.left_derived_obj_iso' F n A.1
      ((homological_complex.Fst C).obj (horseshoe A)) (horseshoe_to_single₁ A)
      (horseshoe_is_projective_resolution₁ A),
    exact this.symm },
  { rw [H₂₃, ← category.assoc, iso.symm_hom, iso.inv_hom_id, category.id_comp],
    simpa },
  { unfold δ,
    dsimp,
    simp only [category.assoc, iso.inv_hom_id_assoc], },
  { ext i,
    apply horseshoe_g_comp_to_single₃_f }
end

lemma exact_of_short_exact.δ_left [F.additive] (n : ℕ) (A : short_exact_sequence C) :
  exact (δ F n A) ((F.left_derived n).map A.f) :=
begin
  let P := map_complex_short_exact_sequence_of_split C F _ (λ i, horseshoe_split A i),
  have := ((homological_complex.six_term_exact_seq n P).drop 2).pair,
  have H₁₂ := functor.left_derived_map_eq' F n A.1 A.2 A.f
    ((homological_complex.Fst C).obj (horseshoe A)) (horseshoe_to_single₁ A)
    ((homological_complex.Snd C).obj (horseshoe A)) (horseshoe_to_single₂ A)
    ((homological_complex.Fst_Snd C).app (horseshoe A))
    (horseshoe_is_projective_resolution₁ A)
    (horseshoe_is_projective_resolution₂ A) _,
  refine preadditive.exact_of_iso_of_exact' _ _ _ _ _ _ _ _ _ this,
  { let := functor.left_derived_obj_iso' F (n+1) A.3
      ((homological_complex.Trd C).obj (horseshoe A)) (horseshoe_to_single₃ A)
      (horseshoe_is_projective_resolution₃ A),
    exact this.symm },
  { let := functor.left_derived_obj_iso' F n A.1
      ((homological_complex.Fst C).obj (horseshoe A)) (horseshoe_to_single₁ A)
      (horseshoe_is_projective_resolution₁ A),
    exact this.symm },
  { let := functor.left_derived_obj_iso' F n A.2
      ((homological_complex.Snd C).obj (horseshoe A)) (horseshoe_to_single₂ A)
      (horseshoe_is_projective_resolution₂ A),
    exact this.symm },
  { unfold δ,
    dsimp,
    simp only [category.assoc, iso.inv_hom_id_assoc], },
  { rw [H₁₂, ← category.assoc, iso.symm_hom, iso.inv_hom_id, category.id_comp],
    simpa },
  { ext i,
    apply horseshoe_f_comp_to_single₂_f }
end

lemma six_term_exact_seq [F.additive] (n : ℕ) (A : short_exact_sequence C) :
  exact_seq D [
    (F.left_derived (n+1)).map A.f, (F.left_derived (n+1)).map A.g,
    δ F n A,
    (F.left_derived n).map A.f, (F.left_derived n).map A.g] :=
begin
  refine exact_seq.cons _ _ (exact_of_short_exact _ _ _) _ _,
  refine exact_seq.cons _ _ (exact_of_short_exact.δ_right _ _ _) _ _,
  refine exact_seq.cons _ _ (exact_of_short_exact.δ_left _ _ _) _ _,
  refine exact_seq.cons _ _ (exact_of_short_exact _ _ _) _ _,
  apply exact_seq.single,
end

end left_derived
end functor
end category_theory
