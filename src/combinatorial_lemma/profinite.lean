import Mbar.functor
import combinatorial_lemma.finite
import algebra.module.linear_map
import pseudo_normed_group.bounded_limits

import category_theory.limits.shapes.products
import topology.category.Compactum

noncomputable theory

open_locale nnreal big_operators

universe u

section
variables (r : ℝ≥0) [fact (0 < r)] (Λ : Type u) [polyhedral_lattice Λ]

open category_theory
open category_theory.limits

lemma polyhedral_exhaustive
  (M : Type*) [pseudo_normed_group M]
  (e : ∀ x : M, ∃ c, x ∈ pseudo_normed_group.filtration M c)
  (x : Λ →+ M) :
  ∃ c : ℝ≥0, x ∈ pseudo_normed_group.filtration (Λ →+ M) c :=
begin
  obtain ⟨ι,hι,l,hl,h⟩ := polyhedral_lattice.polyhedral Λ,
  resetI,
  let cs : ι → ℝ≥0 := λ i, (e (x (l i))).some,
  let c := finset.univ.sup (λ i, cs i / ∥l i∥₊),
  -- This should be easy, using the fact that (l i) ≠ 0.
  have hc : ∀ i, cs i ≤ c * ∥l i∥₊,
  { intro i, rw ← mul_inv_le_iff₀,
    { exact finset.le_sup (finset.mem_univ i), },
    { rw [ne.def, nnnorm_eq_zero], exact h i }, },
  use c,
  rw generates_norm.add_monoid_hom_mem_filtration_iff hl x,
  intros i,
  apply pseudo_normed_group.filtration_mono (hc i),
  apply (e (x (l i))).some_spec,
end

@[simps]
def polyhedral_postcompose {M N : ProFiltPseuNormGrpWithTinv₁ r} (f : M ⟶ N) :
  profinitely_filtered_pseudo_normed_group_with_Tinv_hom r
  (Λ →+ M) (Λ →+ N) :=
{ to_fun := λ x, f.to_add_monoid_hom.comp x,
  map_zero' := by simp only [add_monoid_hom.comp_zero],
  map_add' := by { intros, ext, dsimp, erw [f.to_add_monoid_hom.map_add], refl, },
  strict' := begin
      obtain ⟨ι,hι,l,hl,h⟩ := polyhedral_lattice.polyhedral Λ,
      resetI,
      intros c x hx,
      erw generates_norm.add_monoid_hom_mem_filtration_iff hl at hx ⊢,
      intros i,
      apply f.strict,
      exact hx i,
    end,
  continuous' := λ c, begin
    rw polyhedral_lattice.add_monoid_hom.continuous_iff,
    intro l,
    simp only,
    have aux1 := polyhedral_lattice.add_monoid_hom.incl_continuous Λ r M c,
    have aux2 := f.level_continuous (c * ∥l∥₊),
    exact (aux2.comp (continuous_apply l)).comp aux1,
  end,
  map_Tinv' := λ x, by { ext l, dsimp, rw f.map_Tinv, } }

/-- the functor `M ↦ Hom(Λ, M), where both are considered as objects in
  `ProFiltPseuNormGrpWithTinv₁.{u} r` -/
@[simps]
def hom_functor : ProFiltPseuNormGrpWithTinv₁.{u} r ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r :=
{ obj := λ M,
  { M := Λ →+ M,
    str := infer_instance,
    exhaustive' := by { apply polyhedral_exhaustive, apply M.exhaustive r } },
  map := λ M N f, polyhedral_postcompose _ _ f,
  map_id' := λ M, begin
    ext,
    dsimp [polyhedral_postcompose],
    simp,
  end,
  map_comp' := λ M N L f g, begin
    ext,
    dsimp [polyhedral_postcompose],
    simp,
  end } .

@[simps]
def polyhedral_postcompose' {M N : PseuNormGrp₁} (f : M ⟶ N) :
  strict_pseudo_normed_group_hom (Λ →+ M) (Λ →+ N) :=
{ to_fun := λ x, f.to_add_monoid_hom.comp x,
  map_zero' := by simp only [add_monoid_hom.comp_zero],
  map_add' := by { intros, ext, dsimp, erw [f.to_add_monoid_hom.map_add], refl, },
  strict' := begin
      obtain ⟨ι,hι,l,hl,h⟩ := polyhedral_lattice.polyhedral Λ,
      resetI,
      intros c x hx,
      erw generates_norm.add_monoid_hom_mem_filtration_iff hl at hx ⊢,
      intros i,
      apply f.strict,
      exact hx i,
    end }

@[simps]
def hom_functor' : PseuNormGrp₁.{u} ⥤ PseuNormGrp₁.{u} :=
{ obj := λ M,
  { carrier := Λ →+ M ,
    exhaustive' := by { apply polyhedral_exhaustive, apply M.exhaustive } },
  map := λ M N f, polyhedral_postcompose' _ f,
  map_id' := λ X, by { ext, refl },
  map_comp' := λ X Y Z f g, by { ext, refl } }

open category_theory.limits PseuNormGrp₁

variables {J : Type u} [small_category J] (K : J ⥤ PseuNormGrp₁.{u})

def Ab.limit_cone' {J : Type u} [small_category J] (K : J ⥤ Ab.{u}) :
  limit_cone K :=
⟨Ab.explicit_limit_cone _, Ab.explicit_limit_cone_is_limit _⟩

attribute [simps] to_Ab Ab.limit_cone'

abbreviation hom_functor'_cone_iso_hom_to_fun_aux_to_fun_aux_val_aux (Λ : Type u) {J : Type u}
  [polyhedral_lattice Λ]
  [small_category J]
  (K : J ⥤ PseuNormGrp₁)
  (f : ↥(bounded_cone_point
            (Ab.limit_cone' ((K ⋙ hom_functor' Λ) ⋙ to_Ab))))
  (q : Λ) :
  ↥((Ab.limit_cone' (K ⋙ to_Ab)).cone.X) :=
{ val := λ j, (f.1.1 j).1 q,
  property := begin
    intros a b g,
    have := f.1.2 g,
    dsimp at this ⊢,
    rw ← this, refl,
  end }

abbreviation hom_functor'_cone_iso_hom_to_fun_aux_to_fun_aux (Λ : Type u) {J : Type u}
  [polyhedral_lattice Λ]
  [small_category J]
  (K : J ⥤ PseuNormGrp₁)
  (f : ↥(bounded_cone_point
            (Ab.limit_cone' ((K ⋙ hom_functor' Λ) ⋙ to_Ab)))) :
  Λ → ↥(bounded_cone_point (Ab.limit_cone' (K ⋙ to_Ab))) := λ q,
{ val := hom_functor'_cone_iso_hom_to_fun_aux_to_fun_aux_val_aux Λ _ f q,
  property := begin
    obtain ⟨c,hc⟩ := f.2,
    use c * ∥q∥₊,
    intros j,
    apply hc,
    simp,
  end }

abbreviation hom_functor'_cone_iso_hom_to_fun_aux
  (Λ : Type u) {J : Type u}
  [polyhedral_lattice Λ]
  [small_category J]
  (K : J ⥤ PseuNormGrp₁) :
  ↥(bounded_cone_point
       (Ab.limit_cone' ((K ⋙ hom_functor' Λ) ⋙ to_Ab))) →
  ↥((hom_functor' Λ).obj
       (bounded_cone_point (Ab.limit_cone' (K ⋙ to_Ab)))) := λ f,
{ to_fun := hom_functor'_cone_iso_hom_to_fun_aux_to_fun_aux _ _ f,
  map_zero' := by { ext, simpa },
  map_add' := λ x y, by { ext, simpa } }

def hom_functor'_cone_iso_hom :
  bounded_cone_point (Ab.limit_cone' ((K ⋙ hom_functor' Λ) ⋙ _)) ⟶
  (hom_functor' Λ).obj (bounded_cone_point (Ab.limit_cone' (K ⋙ _))) :=
{ to_fun := hom_functor'_cone_iso_hom_to_fun_aux _ _,
  map_zero' := by { ext, simpa },
  map_add' := λ x y, by { ext, simpa },
  strict' := begin
    intros c x hx,
    obtain ⟨⟨d,hc⟩,rfl⟩ := hx,
    intros e q hq,
    dsimp [bounded_elements.filt_incl],
    delta hom_functor'_cone_iso_hom_to_fun_aux_to_fun_aux,
    delta hom_functor'_cone_iso_hom_to_fun_aux_to_fun_aux_val_aux,
    refine ⟨⟨_,_⟩,rfl⟩,
    intros j,
    apply hc _ hq,
  end }

abbreviation hom_functor'_cone_iso_inv_to_fun_aux_val_aux_val_aux
  (Λ : Type u) {J : Type u}
  [polyhedral_lattice Λ]
  [small_category J]
  (K : J ⥤ PseuNormGrp₁)
  (f : ↥((hom_functor' Λ).obj
            (bounded_cone_point (Ab.limit_cone' (K ⋙ to_Ab))))) :
  Π (j : J), (((K ⋙ hom_functor' Λ) ⋙ to_Ab) ⋙ forget Ab).obj j := λ j,
{ to_fun := λ q, (f.1 q).1.1 j,
  map_zero' := by simpa,
  map_add' := λ x y, by simpa }

abbreviation hom_functor'_cone_iso_inv_to_fun_aux_val_aux
  (Λ : Type u) {J : Type u}
  [polyhedral_lattice Λ]
  [small_category J]
  (K : J ⥤ PseuNormGrp₁)
  (f : ↥((hom_functor' Λ).obj
            (bounded_cone_point (Ab.limit_cone' (K ⋙ to_Ab))))) :
  ↥((Ab.limit_cone' ((K ⋙ hom_functor' Λ) ⋙ to_Ab)).cone.X) :=
{ val := hom_functor'_cone_iso_inv_to_fun_aux_val_aux_val_aux _ _ f,
  property := begin
    intros i j g,
    ext q,
    change Λ →+ _ at f,
    exact (f q).1.2 g,
  end }

abbreviation hom_functor'_cone_iso_inv_to_fun_aux (Λ : Type u) {J : Type u}
  [polyhedral_lattice Λ]
  [small_category J]
  (K : J ⥤ PseuNormGrp₁) :
  ↥((hom_functor' Λ).obj
       (bounded_cone_point (Ab.limit_cone' (K ⋙ to_Ab)))) →
  ↥(bounded_cone_point
       (Ab.limit_cone' ((K ⋙ hom_functor' Λ) ⋙ to_Ab))) := λ f,
{ val := hom_functor'_cone_iso_inv_to_fun_aux_val_aux _ _ f,
  property := begin
    obtain ⟨c,hc⟩ :=
      ((hom_functor' Λ).obj (bounded_cone_point
      (Ab.limit_cone' (K ⋙ to_Ab)))).exhaustive f,
    use c,
    intros j d q hq,
    dsimp [Ab.explicit_limit_cone],
    specialize hc hq,
    obtain ⟨t,ht⟩ := hc,
    rw ← ht,
    apply t.2,
  end }

def hom_functor'_cone_iso_inv :
  (hom_functor' Λ).obj (bounded_cone_point (Ab.limit_cone' (K ⋙ _))) ⟶
  bounded_cone_point (Ab.limit_cone' ((K ⋙ hom_functor' Λ) ⋙ _)) :=
{ to_fun := hom_functor'_cone_iso_inv_to_fun_aux _ _,
  map_zero' := by { ext, simpa },
  map_add' := λ x y, by { ext, simpa },
  strict' := begin
    intros c x hx,
    dsimp,
    refine ⟨⟨_,_⟩,rfl⟩,
    intros j d q hq,
    dsimp [Ab.explicit_limit_cone],
    specialize hx hq,
    obtain ⟨t,ht⟩ := hx,
    rw ← ht,
    apply t.2,
  end }

def hom_functor'_cone_iso_aux :
  bounded_cone_point (Ab.limit_cone' ((K ⋙ hom_functor' Λ) ⋙ _)) ≅
  (hom_functor' Λ).obj (bounded_cone_point (Ab.limit_cone' (K ⋙ _))) :=
{ hom := hom_functor'_cone_iso_hom _ _,
  inv := hom_functor'_cone_iso_inv _ _,
  hom_inv_id' := by { ext, refl },
  inv_hom_id' := by { ext, refl } }

def hom_functor_cone_iso :
  bounded_cone (Ab.limit_cone' ((K ⋙ hom_functor' Λ) ⋙ _)) ≅
  (hom_functor' Λ).map_cone (bounded_cone (Ab.limit_cone' (K ⋙ _))) :=
cones.ext
(hom_functor'_cone_iso_aux _ _) $ λ j, by { ext, refl }

instance : preserves_limits (hom_functor' Λ) :=
begin
  constructor, introsI J hJ, constructor, intros K,
  apply preserves_limit_of_preserves_limit_cone
    (PseuNormGrp₁.bounded_cone_is_limit ⟨_,Ab.explicit_limit_cone_is_limit _⟩),
  refine is_limit.of_iso_limit (PseuNormGrp₁.bounded_cone_is_limit
    ⟨_,Ab.explicit_limit_cone_is_limit _⟩) _,
  apply hom_functor_cone_iso,
end

instance (c) : preserves_limits (hom_functor' Λ ⋙ PseuNormGrp₁.level.obj c) :=
limits.comp_preserves_limits _ _

def ProFiltPseuNormGrpWithTinv₁.to_PNG₁ :
  ProFiltPseuNormGrpWithTinv₁ r ⥤ PseuNormGrp₁ :=
{ obj := λ M,
  { carrier := M,
    exhaustive' := M.exhaustive r },
  map := λ X Y f, { strict' := λ c x h, f.strict h .. f.to_add_monoid_hom } }

/-
def drop_Profinite :
  ProFiltPseuNormGrp₁.{u} ⥤ PseuNormGrp₁.{u} :=
{ obj := λ M,
  { carrier := M,
    exhaustive' := M.exhaustive },
  map := λ X Y f, { strict' := λ c x h, f.strict h .. f.to_add_monoid_hom } }

instance (K : J ⥤ ProFiltPseuNormGrp₁.{u}) : creates_limit K drop_Profinite :=
{ reflects := λ C hC,
  { lift := λ S,
    { continuous' := sorry,
      .. hC.lift (drop_Profinite.map_cone S) },
    fac' := sorry,
    uniq' := sorry },
  lifts := λ S hS,
  { lifted_cone :=
    { X :=
      { M := S.X,
        str :=
        { topology := λ c,
            let
              S' : cone (K ⋙ ProFiltPseuNormGrp₁.level.obj c ⋙ forget _) :=
                (cones.postcompose_equivalence $ eq_to_iso rfl).functor.obj
                ((PseuNormGrp₁.level.obj c).map_cone S),
              hS₁ : is_limit ((PseuNormGrp₁.level.obj c).map_cone S) :=
                is_limit_of_preserves _ hS,
              hS' : is_limit S' :=
                (is_limit.postcompose_hom_equiv _ _).symm hS₁,
              T : cone (K ⋙ ProFiltPseuNormGrp₁.level.obj c) :=
                lift_limit hS',
              hT : is_limit T := lifted_limit_is_limit _,
              E : (forget _).map_cone T ≅ S' := lifted_limit_maps_to_original _,
              e : (forget _).obj T.X ≅ S'.X := (cones.forget _).map_iso E in
              show topological_space S'.X, from
                topological_space.induced e.inv (infer_instance : topological_space T.X),
          t2 := sorry,
          compact := sorry,
          continuous_add' := sorry,
          continuous_neg' := sorry,
          continuous_cast_le := sorry,
          td := sorry,
          ..(infer_instance : pseudo_normed_group S.X) },
          exhaustive' := λ m, S.X.exhaustive _ },
      π :=
      { app := λ j,
        { continuous' := sorry,
          ..(S.π.app j) },
        naturality' := sorry } },
    valid_lift := cones.ext
      { hom :=
        { to_fun := id,
          map_zero' := rfl,
          map_add' := λ _ _, rfl,
          strict' := λ _ _ h, h },
        inv :=
        { to_fun := id,
          map_zero' := rfl,
          map_add' := λ _ _, rfl,
          strict' := λ _ _ h, h },
        hom_inv_id' := by { ext, refl },
        inv_hom_id' := by { ext, refl } }
      begin
        intros j,
        ext, refl,
      end } }

instance : creates_limits drop_Profinite :=
by { constructor, introsI J _, constructor }

instance : preserves_limits drop_Profinite.{u} :=
category_theory.preserves_limits_of_creates_limits_and_has_limits _

-/

def drop_Profinite_drop_Tinv :
  ProFiltPseuNormGrpWithTinv₁.to_PFPNG₁ r ⋙ ProFiltPseuNormGrp₁.to_PNG₁ ≅
  ProFiltPseuNormGrpWithTinv₁.to_PNG₁ r :=
nat_iso.of_components (λ X, iso.refl _) $ by tidy

instance : preserves_limits (ProFiltPseuNormGrpWithTinv₁.to_PNG₁ r) :=
preserves_limits_of_nat_iso (drop_Profinite_drop_Tinv r)

def hom_functor'_forget_iso (c) :
  ProFiltPseuNormGrpWithTinv₁.to_PNG₁ r ⋙ hom_functor' Λ ⋙
  PseuNormGrp₁.level.obj c ≅
  hom_functor _ Λ ⋙ ProFiltPseuNormGrpWithTinv₁.to_PFPNG₁ r ⋙
    ProFiltPseuNormGrp₁.level.obj c ⋙ forget _ :=
nat_iso.of_components (λ X, eq_to_iso rfl) $ by tidy

instance hom_functor_level_preserves_limits (c) : preserves_limits (
  hom_functor r Λ ⋙
  ProFiltPseuNormGrpWithTinv₁.to_PFPNG₁ r ⋙
  ProFiltPseuNormGrp₁.level.obj c ) :=
begin
  apply preserves_limits_of_reflects_of_preserves _ (forget Profinite),
  apply preserves_limits_of_nat_iso (hom_functor'_forget_iso _ _ _),
  change preserves_limits (ProFiltPseuNormGrpWithTinv₁.to_PNG₁ r ⋙
    (hom_functor' Λ ⋙ PseuNormGrp₁.level.obj c)),
  apply limits.comp_preserves_limits,
end

end

/-- Lemma 9.8 of [Analytic] -/
lemma lem98 (r' : ℝ≥0) [fact (0 < r')] [fact (r' < 1)]
  (Λ : Type*) [polyhedral_lattice Λ] (S : Profinite) (N : ℕ) [hN : fact (0 < N)] :
  pseudo_normed_group.splittable (Λ →+ (Mbar.functor r').obj S) N (lem98.d Λ N) :=
begin
  -- This reduces to `lem98_finite`: See the first lines of the proof in [Analytic].
  sorry
end
