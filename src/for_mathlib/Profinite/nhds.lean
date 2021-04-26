import for_mathlib.Profinite.functorial_limit

namespace Profinite

open category_theory

universe u

variables (X B : Profinite.{u}) (f : X ⟶ B)

lemma nhds_of_limit {J : Type u} [small_category J] (F : J ⥤ Profinite.{u})
  (a : (limit_cone F).cone.X) : nhds a =
  ⨅ (i : J), filter.comap ((limit_cone F).cone.π.app i) (nhds $ (limit_cone F).cone.π.app i a) :=
begin
  let P := Π (j : J), F.obj j,
  have : nhds (a.val : P) = ⨅ (i : J), filter.comap (λ x, x i) (nhds (a.val i)),
  apply nhds_pi,
  erw [nhds_subtype, this],
  rw filter.comap_infi,
  congr, funext i,
  have : (λ X : P, X i) ∘ subtype.val = (limit_cone F).cone.π.app i, refl,
  simpa [← this, filter.comap_comap],
end

def homeo_of_iso {X Y : Profinite} (f : X ≅ Y) : X ≃ₜ Y :=
{ to_fun := f.hom,
  inv_fun := f.inv,
  left_inv := λ x, by {change (f.hom ≫ f.inv) x = x, simp},
  right_inv := λx, by {change (f.inv ≫ f.hom) x = x, simp},
  continuous_to_fun := f.hom.continuous,
  continuous_inv_fun := f.inv.continuous }

lemma nhds_of_homeo {X Y : Type*} [topological_space X] [topological_space Y]
  (f : X ≃ₜ Y) (a : X) : nhds a = filter.comap f (nhds $ f a) := by simp


lemma nhds_eq_infi (a : X) : nhds a = ⨅ (I : X.clopen_cover), filter.comap I.proj (nhds $ I.proj a) :=
begin
  haveI := X.is_iso_lift,
  let : X ≅ (limit_cone $ X.diagram ⋙ of_Fintype).cone.X :=
    as_iso ((limit_cone (X.diagram ⋙ of_Fintype)).is_limit.lift X.Fincone),
  let f := homeo_of_iso this,
  have := nhds_of_limit (X.diagram ⋙ of_Fintype) (f a),
  rw nhds_of_homeo f,
  rw this,
  simp,
  congr,
  funext i,
  let P := Π (I : X.clopen_cover), I,
  have : (λ x : P, x i) ∘ subtype.val ∘ f = i.proj, refl,
  rw ← this,
  simp [filter.comap_comap],
  refl,
end

/-
lemma nhds_basis (a : X) : (nhds a).has_basis (λ S, a ∈ S ∧ is_clopen S) id :=
begin
  rw nhds_eq_infi,
  constructor,
  intros S,
  split,
  { intro h,
    rw filter.mem_infi_iff at h,
    rcases h with ⟨T,hT,V,hV1,hV2⟩,
    let W := ⋂ (t : T), V t,
    refine ⟨W,⟨_,_⟩,hV2⟩,
    have := fintype.of_finset hT.to_finset,
    have := @is_clopen_Inter X _ _ T',
    have := @is_clopen_bInter X _ _ hT.to_finset,
  },
  { sorry }
end
-/

lemma pullback_map_injective (I : B.clopen_cover) :
  function.injective (clopen_cover.map I.pullback_le_rel : I.pullback f → I) :=
begin
  intros U V h,
  apply clopen_cover.eq_of_le,
  intros a ha,
  have hU := clopen_cover.map_spec (I.pullback_le_rel : clopen_cover.le_rel f _ _) U ha,
  rw h at hU,
  rcases (clopen_cover.pullback_spec V) with ⟨W,h1,h2⟩,
  rw h1,
  convert hU,
  apply clopen_cover.map_unique,
  refine le_of_eq h1,
end

end Profinite
