import for_mathlib.derived_functor
import category_theory.abelian.left_derived

universes w v u

noncomputable theory

namespace category_theory.abelian.functor

open category_theory category_theory.functor category_theory.limits
open category_theory.functor.left_derived

variables {C : Type u} {D : Type u} [category.{w} C] [category.{w} D] [enough_projectives C]
variables (F : C ⥤ D) {A₁ A₂ A₃ X : C} {f : A₁ ⟶ A₂} {g : A₂ ⟶ A₃}
variables [abelian C] [abelian D] [additive F] [preserves_finite_colimits F]

section les

def δ₀ (A : short_exact_sequence C) := δ F 0 A ≫ (left_derived_zero_iso_self F).hom.app A.1

lemma seven_term_exact_seq (A : short_exact_sequence C) :
  exact_seq D [
    (F.left_derived 1).map A.f, (F.left_derived 1).map A.g,
    δ₀ F A,
    F.map A.f, F.map A.g, (0 : F.obj A.3 ⟶ F.obj A.3)] :=
begin
  refine exact_seq.cons _ _ (exact_of_short_exact _ _ _) _ (exact_seq.cons _ _ _ _ _),
  { refine preadditive.exact_of_iso_of_exact' ((F.left_derived 1).map A.g) (δ F 0 A) _ _
      (iso.refl _) (iso.refl _) ((left_derived_zero_iso_self F).app A.1) (by simp) _ _,
    { dsimp [δ₀], rw [category.id_comp] },
    { exact (exact_iff_exact_seq _ _).2 ((six_term_exact_seq F 0 A).extract 1 2) } },
  refine exact_seq.cons _ _ _ _ _,
  { refine preadditive.exact_of_iso_of_exact' (δ F 0 A) ((F.left_derived 0).map A.f) _ _
      (iso.refl _) ((left_derived_zero_iso_self F).app A.1) ((left_derived_zero_iso_self F).app A.2)
      _ (by simp) _,
    { dsimp [δ₀], rw [category.id_comp] },
    { exact (exact_iff_exact_seq _ _).2 ((six_term_exact_seq F 0 A).extract 2 2) } },
    apply exact_seq.cons,
    { exact preserves_exact_of_preserves_finite_colimits_of_epi _ A.exact' },
    { rw [← exact_iff_exact_seq],
      exact ((abelian.tfae_epi (F.obj A.3) (F.map A.g)).out 0 2).1
        (category_theory.preserves_epi _ _) }
end

end les

end category_theory.abelian.functor
