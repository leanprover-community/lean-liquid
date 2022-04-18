import condensed.adjunctions
import category_theory.adjunction.evaluation

open category_theory
open category_theory.grothendieck_topology
open opposite

universe u

variables (F : Profinite.{u}ᵒᵖ ⥤ Ab.{u+1}) (G : Condensed.{u} Ab.{u+1})
variables (η : F ⟶ G.val)

instance {α : Type u} : limits.has_coproducts_of_shape α Ab.{u+1} := sorry

theorem Condensed_Ab_sheafify_lift_mono_of_exists :
  (∀ (B : Profinite.{u}) (t : F.obj (op B)), η.app (op B) t = 0 →
    (∃ (α : Type u) [fintype α] (X : α → Profinite.{u}) (π : Π a : α, X a ⟶ B)
      (surj : ∀ b : B, ∃ (a : α) (x : X a), π a x = b),
      ∀ a : α, F.map (π a).op t = 0)) → mono (proetale_topology.sheafify_lift η G.cond) :=
begin
  intros h,
  rw nat_trans.mono_iff_app_mono, intros B, tactic.op_induction',
  -- Missing?
  suffices : function.injective ((proetale_topology.sheafify_lift η G.cond).app (op B)), sorry,
  rw add_monoid_hom.injective_iff, intros t ht,
  obtain ⟨W,E,rfl⟩ := limits.concrete.colimit_exists_rep _ t,
  let E' := limits.concrete.multiequalizer_equiv _ E,
  sorry,
end
