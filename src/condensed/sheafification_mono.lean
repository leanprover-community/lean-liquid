import condensed.adjunctions
import category_theory.adjunction.evaluation

universe u
variables (F : Profinite.{u}ᵒᵖ ⥤ Ab.{u+1}) (G : Condensed.{u} Ab.{u+1})
variables (η : F ⟶ G.val)

open category_theory
open category_theory.grothendieck_topology
open opposite

instance {α : Type u} : limits.has_coproducts_of_shape α Ab.{u+1} := sorry

theorem sheafify_lift_mono_iff :
  mono (sheafify_lift _ η G.cond) ↔
  ∀ (B : Profinite.{u}) (t : F.obj (op B)), η.app (op B) t = 0 →
    (∃ (α : Type u) [fintype α] (X : α → Profinite.{u}) (π : Π a : α, X a ⟶ B)
      (surj : ∀ b : B, ∃ (a : α) (x : X a), π a x = b),
      ∀ a : α, F.map (π a).op t = 0) :=
begin
  rw nat_trans.mono_iff_app_mono,
  split,
  { intros h B t ht, sorry },
  { intros h B, tactic.op_induction',
    -- Is this missing?
    suffices : function.injective ((proetale_topology.sheafify_lift η G.cond).app (op B)), sorry,
    rw add_monoid_hom.injective_iff, intros t ht,
    specialize h B, sorry },
end
