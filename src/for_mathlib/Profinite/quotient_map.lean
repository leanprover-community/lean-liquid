import topology.category.Profinite

namespace Profinite

-- A surjective map of compact Hausdorff spaces is a quotient map
-- TODO: This certainly belongs in mathlib, if not already there...
lemma quotient_map {X Y : Profinite} (f : X ⟶ Y) (hf : function.surjective f) :
  quotient_map f :=
begin
  rw quotient_map_iff,
  refine ⟨hf,_⟩,
  intro S,
  refine ⟨λ hS, hS.preimage f.continuous, λ hS, _⟩,
  rw ← is_closed_compl_iff at *,
  rw ← set.preimage_compl at hS,
  have : Sᶜ = f '' (f ⁻¹' Sᶜ),
  { ext,
    split,
    { intro h,
      obtain ⟨y,rfl⟩ := hf x,
      refine ⟨y,h,rfl⟩ },
    { rintro ⟨y,h,rfl⟩,
      exact h } },
  rw this,
  exact Profinite.is_closed_map f (⇑f ⁻¹' Sᶜ) hS
end

end Profinite
