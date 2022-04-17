import condensed.adjunctions

universe u
variables (F : Profinite.{u}ᵒᵖ ⥤ Ab.{u+1}) (G : Condensed.{u} Ab.{u+1})
variables (η : F ⟶ G.val)

open category_theory
open category_theory.grothendieck_topology
open opposite

theorem sheafify_lift_mono_iff :
  mono (sheafify_lift _ η G.cond) ↔
  ∀ (B : Profinite.{u}) (t : F.obj (op B)), η.app (op B) t = 0 →
    (∃ (α : Type u) [fintype α] (X : α → Profinite.{u}) (π : Π a : α, X a ⟶ B)
      (surj : ∀ b : B, ∃ (a : α) (x : X a), π a x = b),
      ∀ a : α, F.map (π a).op t = 0) := sorry
