import condensed.adjunctions
import category_theory.adjunction.evaluation
import for_mathlib.sheafification_mono

open category_theory
open category_theory.grothendieck_topology
open opposite

universe u

variables (F : Profinite.{u}ᵒᵖ ⥤ Ab.{u+1}) (G : Condensed.{u} Ab.{u+1})
variables (η : F ⟶ G.val)

theorem Condensed_Ab_sheafify_lift_mono_of_exists :
  (∀ (B : Profinite.{u}) (t : F.obj (op B)), η.app (op B) t = 0 →
    (∃ (α : Type u) [fintype α] (X : α → Profinite.{u}) (π : Π a : α, X a ⟶ B)
      (surj : ∀ b : B, ∃ (a : α) (x : X a), π a x = b),
      ∀ a : α, F.map (π a).op t = 0)) → mono (proetale_topology.sheafify_lift η G.cond) :=
begin
  intros h,
  apply sheafify_lift_mono_of_exists_cover,
  intros B t ht,
  specialize h B t ht,
  obtain ⟨α, hα, X, π, surj, h⟩ := h,
  resetI,
  let W : proetale_topology.cover B := ⟨sieve.generate (presieve.of_arrows X π), _⟩,
  use W,
  rintros ⟨Z,f,⟨A,g,hg,⟨a⟩,rfl⟩⟩,
  dsimp, simp [h a],
  use [presieve.of_arrows X π, α, hα, X, π, surj],
  apply sieve.le_generate,
end

theorem presheaf_to_Condensed_Ab_map_mono_of_exists
  (h : ∀ (B : Profinite.{u}) (t : F.obj (op B)), η.app (op B) t = 0 →
    (∃ (α : Type u) [fintype α] (X : α → Profinite.{u}) (π : Π a : α, X a ⟶ B)
      (surj : ∀ b : B, ∃ (a : α) (x : X a), π a x = b),
      ∀ a : α, F.map (π a).op t = 0)):
  mono (((sheafification_adjunction
    proetale_topology Ab.{u+1}).hom_equiv _ G).symm η) :=
begin
  apply faithful_reflects_mono (Sheaf_to_presheaf proetale_topology Ab.{u+1}),
  dsimp [sheafification_adjunction],
  apply Condensed_Ab_sheafify_lift_mono_of_exists,
  exact h
end
