import for_mathlib.endomorphisms.basic
import for_mathlib.exact_functor

universe v

namespace category_theory

namespace endomorphisms

open homological_complex category_theory category_theory.limits category

variables (𝓐 : Type*) [category.{v} 𝓐]

@[simps]
def tautological_nat_trans :
  (endomorphisms.forget 𝓐) ⟶ (endomorphisms.forget 𝓐) :=
{ app := λ X, X.e, }

variable {𝓐}

variables [abelian 𝓐]
  [has_coproducts_of_shape (ulift.{v} ℕ) 𝓐] [has_products_of_shape (ulift.{v} ℕ) 𝓐]
variables {M : Type*} {c : complex_shape M} (F : endomorphisms 𝓐 ⥤ homological_complex 𝓐 c)
variables (Y : homological_complex (endomorphisms 𝓐) c)

@[simps]
def _root_.homological_complex.tautological_endomorphism : Y ⟶ Y :=
{ f := λ i, ⟨(Y.X i).e, rfl⟩, }

lemma homology_functor_obj_e (i : M) :
  ((homology_functor (endomorphisms 𝓐) c i).obj Y).e =
    ((homology_functor (endomorphisms 𝓐) c i).map Y.tautological_endomorphism).f  :=
begin
  have h₁ := ((endomorphisms.forget 𝓐).homology_functor_iso c i).hom.naturality
    Y.tautological_endomorphism,
  rw [← cancel_mono (((endomorphisms.forget 𝓐).homology_functor_iso c i).inv.app Y),
    assoc] at h₁,
  conv_lhs at h₁ { congr, skip, rw [← nat_trans.comp_app, iso.hom_inv_id, nat_trans.id_app], },
  rw comp_id at h₁,
  conv_lhs at h₁ { dsimp only [functor.comp, endomorphisms.forget], },
  rw h₁,
  clear h₁,
  have h₂ := nat_trans.congr_app (functor.naturality_homology_functor_iso
    (tautological_nat_trans 𝓐) c i) Y,
  dsimp [nat_trans.hcomp] at h₂,
  rw [comp_id, id_comp, ← cancel_mono
    (((endomorphisms.forget 𝓐).homology_functor_iso c i).inv.app Y), assoc] at h₂,
  conv_lhs at h₂ { congr, skip, rw [← nat_trans.comp_app, iso.hom_inv_id, nat_trans.id_app], },
  erw comp_id at h₂,
  exact h₂,
end

end endomorphisms

end category_theory
