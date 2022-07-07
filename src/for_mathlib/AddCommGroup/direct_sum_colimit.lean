import for_mathlib.AddCommGroup.explicit_products

open category_theory
open category_theory.limits

namespace AddCommGroup

universes u
variables {J : Type u} [small_category J] (F : J ⥤ AddCommGroup.{u})

open_locale classical
noncomputable theory

def explicit_cocone_point_kernel :
  add_subgroup (direct_sum J (λ i, F.obj i)) :=
add_subgroup.closure
{ x | ∃ (i j : J) (f : i ⟶ j) (t : F.obj i),
  x = direct_sum.of _ j (F.map f t) - direct_sum.of _ i t  }

def as_small_succ (i : as_small.{u} ℕ) : as_small ℕ :=
  as_small.up.obj (as_small.down.obj i + 1)

def to_as_small_succ (i : as_small.{u} ℕ) : i ⟶ as_small_succ i :=
as_small.up.map (hom_of_le $ nat.le_succ _)

lemma explicit_cocone_point_kernel_eq_of_as_small_nat
  (F : as_small.{u} ℕ ⥤ AddCommGroup.{u}) :
  explicit_cocone_point_kernel F =
  add_subgroup.closure { x | ∃ i (t : F.obj i), x =
    direct_sum.of (λ i, F.obj i) (as_small_succ i) (F.map (to_as_small_succ i) t) -
    direct_sum.of _ i t } :=
begin
  apply le_antisymm,
  { erw add_subgroup.closure_le,
    rintros x ⟨⟨i⟩,⟨j⟩,f,t,rfl⟩,
    obtain ⟨k,rfl⟩ : ∃ k : ℕ, j = i + k,
    { have : i ≤ j := le_of_hom (as_small.down.map f),
      exact le_iff_exists_add.mp this },
    induction k with k hk,
    { have : f = 𝟙 _, ext, rw this,
      simp only [category_theory.functor.map_id, id_apply, set_like.mem_coe],
      erw sub_self,
      exact add_subgroup.zero_mem _, },
    { let f₁ : as_small.up.obj i ⟶ as_small.up.obj (i + k) := as_small.up.map
        (hom_of_le $ le_self_add),
      let f₂ : as_small.up.obj (i + k) ⟶ as_small.up.obj (i + (k + 1)) :=
        as_small.up.map (hom_of_le $ by nlinarith),
      have hf : f = f₁ ≫ f₂, by ext, rw hf, clear hf,
      specialize hk f₁,
      let t' := _, change t' ∈ _, let s := _, change s ∈ _ at hk,
      rw (show t' = (t' - s) + s, by simp),
      let A := add_subgroup.closure {x :
        direct_sum (as_small ℕ) (λ (i : as_small ℕ), ↥(F.obj i)) |
          ∃ (i : as_small ℕ) (t : ↥(F.obj i)), x =
            (direct_sum.of (λ (i : as_small ℕ), ↥(F.obj i)) (as_small_succ i))
              ((F.map (to_as_small_succ i)) t) -
            (direct_sum.of (λ (i : as_small ℕ), ↥(F.obj i)) i) t},
      change _ ∈ A,
      suffices : (t' - s) ∈ A, by exact A.add_mem this hk,
      dsimp [t', s], simp only [functor.map_comp, comp_apply, sub_sub_sub_cancel_right],
      apply add_subgroup.subset_closure,
      use as_small.up.obj (i + k),
      let tt : F.obj (as_small.up.obj (i + k)) := F.map f₁ t,
      use tt,
      congr } },
  { rw add_subgroup.closure_le,
    rintros x ⟨i,t,rfl⟩,
    apply add_subgroup.subset_closure,
    refine ⟨i,as_small_succ i, to_as_small_succ i, t, _⟩,
    congr }
end

def explicit_cocone_point : AddCommGroup.{u} :=
AddCommGroup.of
((direct_sum J (λ i, F.obj i)) ⧸ explicit_cocone_point_kernel F)

def explicit_cocone : cocone F :=
{ X := explicit_cocone_point F,
  ι :=
  { app := λ j, add_monoid_hom.comp (quotient_add_group.mk' _)
      (direct_sum.of _ j),
    naturality' := begin
      intros i j f, ext t,
      simp only [comp_apply, add_monoid_hom.coe_comp,
        quotient_add_group.coe_mk', function.comp_app, functor.const.obj_map,
        id_apply],
      rw quotient_add_group.eq_iff_sub_mem,
      apply add_subgroup.subset_closure,
      dsimp, refine ⟨i, j, f, t, rfl⟩,
    end } }

def is_colimit_explicit_cocone : is_colimit (explicit_cocone F) :=
{ desc := λ S, quotient_add_group.lift _
    (direct_sum.to_add_monoid $ λ i, S.ι.app _)
    begin
      intros t ht,
      apply add_subgroup.closure_induction ht,
      { rintros x ⟨i,j,f,t,rfl⟩,
        simp only [map_sub, direct_sum.to_add_monoid_of, cocone.w_apply, sub_self] },
      { simp only [map_zero], },
      { intros x y hx hy, simp only [hx, hy, map_add, add_zero] },
      { intros x hx, simp only [hx, map_neg, neg_zero] },
    end,
  fac' := begin
    intros S j, ext t, dsimp [explicit_cocone],
    simp only [direct_sum.to_add_monoid_of, comp_apply, add_monoid_hom.coe_comp,
      quotient_add_group.coe_mk', quotient_add_group.lift_mk],
  end,
  uniq' := begin
    intros S m hm, ext j t,
    simp only [direct_sum.to_add_monoid_of, add_monoid_hom.coe_comp, quotient_add_group.coe_mk',
      function.comp_app, quotient_add_group.lift_mk],
    rw ← hm, refl,
  end }

end AddCommGroup
