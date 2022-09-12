import condensed.top_comparison
import condensed.exact
.

open category_theory opposite

def compactly_generated
  (X : Type)
  [topological_space X] :
  Prop :=
∀ (U : set X),
  is_open U ↔
  (∀ (S : Profinite.{0})
    (f : S → X)
    (hf : continuous f),
    is_open (f ⁻¹' U))

@[simps {fully_applied := ff}]
def Top_to_condensed_pts (X : Top.{0}) :
  X.to_Condensed.val.obj
    (op (Profinite.punit)) ≃ X :=
{ to_fun := λ s, s.down.to_fun punit.star,
  inv_fun := λ x, ⟨⟨function.const _ x⟩⟩,
  left_inv := by { rintro ⟨s⟩, ext ⟨⟩, refl },
  right_inv := by { intro x, refl } }

lemma Top_to_Condensed_full'
  (X Y : Top)
  (hX : compactly_generated X)
  (α : X.to_Condensed ⟶ Y.to_Condensed) :
  ∃ f : X ⟶ Y, Top_to_Condensed.map f = α :=
begin
  let f : X → Y :=
    (Top_to_condensed_pts Y) ∘
    α.val.app (op Profinite.punit) ∘
    (Top_to_condensed_pts X).symm,
  suffices hf : continuous f,
  { refine ⟨⟨f,hf⟩, _⟩,
    ext S x s,
    have := α.val.naturality
      (Profinite.from_punit s).op,
    apply_fun (λ φ, (φ x).down.to_fun punit.star) at this,
    -- dsimp [f] at this ⊢,
    exact this, },
  rw continuous_def,
  assume U hU,
  rw hX,
  assume S g hg,
  rw [← set.preimage_comp],
  suffices : continuous (f ∘ g),
  { exact continuous_def.mp this U hU, },
  let g' := α.val.app (op S) ⟨⟨g, hg⟩⟩,
  suffices : f ∘ g = g'.down.to_fun,
  { rw this, exact g'.down.continuous },
  ext s,
  have := α.val.naturality
    (Profinite.from_punit s).op,
  apply_fun (λ φ, (φ ⟨⟨g, hg⟩⟩).down.to_fun punit.star) at this,
  -- dsimp [f, g'] at this ⊢,
  exact this,
end
