import for_mathlib.Profinite.functorial_limit
import locally_constant.NormedGroup

noncomputable theory

namespace NormedGroup

open opposite locally_constant category_theory

universes u

variables (M : NormedGroup.{u}) (X : Profinite.{u})

def lc_to_discrete_quotient (f : locally_constant X M) :
  discrete_quotient X :=
{ rel := λ a b, f a = f b,
  equiv := ⟨by tauto, by tauto, λ a b c h1 h2, by rw [h1, h2]⟩,
  clopen := λ x, ⟨is_locally_constant _ _,
    ⟨by {erw ← set.preimage_compl, apply is_locally_constant _ _}⟩⟩ }

def lc_desc (f : locally_constant X M) :
  locally_constant (lc_to_discrete_quotient _ _ f) M :=
{ to_fun := λ i, quotient.lift_on' i f (by tauto),
  is_locally_constant := λ U, is_open_discrete _ }

lemma lc_factors (f : locally_constant X M) : (lc_desc _ _ f) ∘
  (lc_to_discrete_quotient _ _ f).proj = f := rfl

abbreviation diagram : NormedGroup ⥤ (discrete_quotient X)ᵒᵖ ⥤ NormedGroup :=
LocallyConstant ⋙ (whiskering_left _ _ _).obj (X.diagram ⋙ Fintype_to_Profinite).op

end NormedGroup
