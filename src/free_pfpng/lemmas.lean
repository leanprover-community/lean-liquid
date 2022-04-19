import free_pfpng.basic
import pseudo_normed_group.bounded_limits
import condensed.adjunctions
import for_mathlib.AddCommGroup

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

lemma discrete_quotient_separates_points {α : Type*} [fintype α] {S : Profinite}
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

open category_theory

theorem discrete_quotient_separates_points (S : Profinite) (t₁ t₂ : S.free_pfpng)
  (h : ∀ T : discrete_quotient S, S.free_pfpng_π T t₁ = S.free_pfpng_π T t₂) : t₁ = t₂ :=
begin
  let E : limits.cone ((S.fintype_diagram ⋙ free_pfpng_functor) ⋙
      ProFiltPseuNormGrp₁.to_PNG₁ ⋙ PseuNormGrp₁.to_Ab) :=
    Ab.explicit_limit_cone _,
  let hE : limits.is_limit E := Ab.explicit_limit_cone_is_limit _,
  let B := ProFiltPseuNormGrp₁.bounded_cone ⟨E,hE⟩,
  let hB : limits.is_limit B := ProFiltPseuNormGrp₁.bounded_cone_is_limit ⟨E,hE⟩,
  let II : limits.limit.cone _ ≅ B := (limits.limit.is_limit _).unique_up_to_iso hB,
  let I : S.free_pfpng ≅ B.X := (limits.cones.forget _).map_iso II,
  apply_fun I.hom, ext T : 3, exact h T,
  intros x y hh, apply_fun (λ e, I.inv e) at hh,
  change (I.hom ≫ I.inv) x = (I.hom ≫ I.inv) y at hh,
  simpa only [iso.hom_inv_id] using hh,
end

end free_pfpng

namespace free_pfpng

open AddCommGroup

universe u

/--
If `t₁ t₂ : ℤ[S]` have the same image in `ℤ[T]` for every discrete quotient `T` of `S`,
then `t₁ = t₂`. Here `ℤ[-]` refers to the usual free abelian group of the *set* `S`.
-/
def discrete_quotient_separates_points' (S : Profinite.{u})
  (t : free'.obj S) (h : ∀ T : discrete_quotient S, free'.map T.proj t = 0) : t = 0 :=
begin
  let A := t.support,
  let e : A → ℤ := λ a, t.to_fun a,
  let ι : A → S := λ a, a,
  have hι : function.injective ι,
  { intros x y h, ext, exact h },
  obtain ⟨T,hT⟩ := Profinite.discrete_quotient_separates_points ι hι,
  specialize h T,
  let t' : A →₀ ℤ := t.comap_domain ι _,
  swap, { apply hι.inj_on },
  let q : T →₀ ℤ := free'.map T.proj t,
  let π : A → T := T.proj ∘ ι,
  let q' : A →₀ ℤ := q.comap_domain π _,
  swap, { apply hT.inj_on },
  suffices : t' = q',
  { ext i, by_cases hi : i ∈ A,
    swap, { rwa finsupp.not_mem_support_iff at hi },
    let j : A := ⟨i,hi⟩, change t' j = 0, rw this,
    let t : T := T.proj i, apply_fun (λ e, e.to_fun t) at h,
    exact h },
  classical,
  ext a, dsimp [t', q', ι, q, π, finsupp.map_domain],
  simp only [finsupp.sum_apply],
  dsimp [finsupp.sum, finsupp.single],
  erw finset.sum_ite, simp,
  convert (@finset.sum_singleton ℤ S a t.to_fun _).symm,
  rw finset.eq_singleton_iff_unique_mem,
  split,
  { rw finset.mem_filter,
    exact ⟨a.2, rfl⟩ },
  { intros x hx, rw finset.mem_filter at hx,
    let x' : A := ⟨x,hx.1⟩,
    change ι x' = ι a,
    congr' 1, apply hT, exact hx.2 }
end

end free_pfpng
