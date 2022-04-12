import free_pfpng.basic
import pseudo_normed_group.bounded_limits
import condensed.adjunctions
import algebra.category.Module.adjunctions
import group_theory.free_abelian_group_finsupp

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

-- Move this
namespace AddCommGroup

noncomputable theory
universe u

@[simps]
def free' : Type u ⥤ AddCommGroup.{u} :=
{ obj := λ X, AddCommGroup.of $ X →₀ ℤ,
  map := λ X Y f, finsupp.map_domain.add_monoid_hom f,
  map_id' := sorry, -- easy
  map_comp' := sorry -- easy
}

@[simps]
def of_iso {A B : Type u} [add_comm_group A] [add_comm_group B]
  (e : A ≃+ B) : of A ≅ of B :=
{ hom := e.to_add_monoid_hom,
  inv := e.symm.to_add_monoid_hom,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }

@[simps]
def free_iso_free' : free ≅ free' :=
category_theory.nat_iso.of_components
(λ X, of_iso (free_abelian_group.equiv_finsupp X))
sorry

def adj' : free' ⊣ category_theory.forget _ :=
AddCommGroup.adj.of_nat_iso_left $ free_iso_free'

end AddCommGroup
