import condensed.adjunctions
import category_theory.adjunction.evaluation

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
  sorry,
end
