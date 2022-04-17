import condensed.adjunctions
import category_theory.adjunction.evaluation

open category_theory
open category_theory.grothendieck_topology
open opposite

universe u

section for_mathlib

lemma AddCommGroup.mono_iff_injective {X Y : AddCommGroup} (f : X ⟶ Y) :
  mono f ↔ function.injective f := sorry

instance {α : Type u} : limits.has_coproducts_of_shape α Ab.{u+1} := sorry

variables {C : Type (u+1)} [category.{u} C] (J : grothendieck_topology C)
  (F : Cᵒᵖ ⥤ Ab.{u+1}) (G : Sheaf J Ab.{u+1}) (η : F ⟶ G.val)

theorem sheafify_lift_mono_iff :
  mono (sheafify_lift J η G.cond) ↔
  ∀ (B : C) (t : F.obj (op B)), η.app (op B) t = 0 →
  (∃ W : (J.cover B), ∀ f : W.arrow, F.map f.f.op t = 0) :=
begin
  rw nat_trans.mono_iff_app_mono,
  split,
  { intros h B t ht,
    replace h : ∀ B : C, ((J.sheafify_lift η G.cond).app (op B)).ker = ⊥, sorry,
    sorry },
  { intros h B, tactic.op_induction',
    -- Is this missing?
    suffices : function.injective ((J.sheafify_lift η G.cond).app (op B)), sorry,
    rw add_monoid_hom.injective_iff, intros t ht,
    specialize h B, sorry },
end

end for_mathlib

variables (F : Profinite.{u}ᵒᵖ ⥤ Ab.{u+1}) (G : Condensed.{u} Ab.{u+1})
variables (η : F ⟶ G.val)

theorem Condensed_Ab_sheafify_lift_mono_iff :
  mono (sheafify_lift _ η G.cond) ↔
  ∀ (B : Profinite.{u}) (t : F.obj (op B)), η.app (op B) t = 0 →
    (∃ (α : Type u) [fintype α] (X : α → Profinite.{u}) (π : Π a : α, X a ⟶ B)
      (surj : ∀ b : B, ∃ (a : α) (x : X a), π a x = b),
      ∀ a : α, F.map (π a).op t = 0) :=
begin
  rw sheafify_lift_mono_iff proetale_topology.{u},
  sorry,
end
