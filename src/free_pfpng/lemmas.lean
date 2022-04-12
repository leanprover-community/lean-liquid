import free_pfpng.basic

-- Move this
namespace Profinite

def pt {S : Profinite} (x : S) : Profinite.of punit ⟶ S := ⟨λ _, x⟩

lemma discrete_quotient_separates_points_aux
  {S : Profinite} {x y : S} (h : x ≠ y) : ∃ T : discrete_quotient S,
    T.proj x ≠ T.proj y :=
begin
  contrapose! h,
  let x' := Profinite.pt x,
  let y' := Profinite.pt y,
  suffices : x' = y',
  { change x' punit.star = y' punit.star, rw this },
  apply S.as_limit.hom_ext, intros T, specialize h T,
  ext, exact h,
end

lemma discrete_quotient_separates_points {α : Fintype} {S : Profinite}
  (f : α → S) (hf : function.injective f) :
  ∃ (T : discrete_quotient S), function.injective (T.proj ∘ f) :=
begin
  classical,
  let e : Π (a b : α) (h : a ≠ b), { x : S × S | x.1 ≠ x.2 } := λ a b h, ⟨⟨_,_⟩, hf.ne h⟩,
  choose T hT using (λ a b h, discrete_quotient_separates_points_aux (e a b h).2),
  obtain ⟨E,hE⟩ : ∃ E : discrete_quotient S, ∀ a b h, E ≤ T a b h,
  { let E : discrete_quotient S := (finset.univ : finset ↥{x : α × α | x.1 ≠ x.2}).inf
      (λ x, T x.1.1 x.1.2 x.2),
    use E, intros a b h,
    let i : {x : α × α | x.1 ≠ x.2} := ⟨⟨a,b⟩,h⟩,
    have hi : i ∈ finset.univ := by refine finset.mem_univ i,
    exact finset.inf_le hi },
  use E, intros a b h,
  specialize hT a b, contrapose h, intros c, apply hT h,
  apply_fun (discrete_quotient.of_le (hE a b h)) at c, exact c,
end

end Profinite

namespace free_pfpng

end free_pfpng
