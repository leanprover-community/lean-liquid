import condensed.extr.basic
import topology.category.CompHaus.projective

noncomputable theory

open category_theory

namespace ExtrDisc

lemma lift_exists' {X Y : CompHaus} {P : ExtrDisc} (f : X ⟶ Y)
  (hf : function.surjective f) (e : P.val.to_CompHaus ⟶ Y) :
  ∃ g : P.val.to_CompHaus ⟶ X, g ≫ f = e :=
begin
  have : epi f := by rwa CompHaus.epi_iff_surjective f,
  let B : Profinite := Profinite.of (ultrafilter P.val),
  let π : B ⟶ P.val := ⟨_, continuous_ultrafilter_extend id⟩,
  have : epi π,
  { rw Profinite.epi_iff_surjective,
    intro x, refine ⟨(pure x : ultrafilter P.val), _⟩,
    have := @ultrafilter_extend_extends P.val _ _ _ id,
    exact congr_fun this x, },
  resetI,
  choose s hs using projective.factors (𝟙 _) π,
  let φ : CompHaus.of (ultrafilter P.val.to_CompHaus) ⟶ Y := π ≫ e,
  choose g h using projective.factors φ f,
  refine ⟨s ≫ g, _⟩,
  erw [category.assoc, h, ← category.assoc, hs, category.id_comp],
end

def lift' {X Y : CompHaus} {P : ExtrDisc} (f : X ⟶ Y)
  (hf : function.surjective f) (e : P.val.to_CompHaus ⟶ Y) : P.val.to_CompHaus ⟶ X :=
(lift_exists' f hf e).some

@[simp, reassoc]
lemma lift_lifts' {X Y : CompHaus} {P : ExtrDisc} (f : X ⟶ Y)
  (hf : function.surjective f) (e : P.val.to_CompHaus ⟶ Y) :
  lift' f hf e ≫ f = e :=
(lift_exists' f hf e).some_spec

end ExtrDisc
