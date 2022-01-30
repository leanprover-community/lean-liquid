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

/-
-- Sanity check using Mathlib PR: #11690
example : creates_limits
  (forget Profinite.{u}) := infer_instance

lemma polyhedral_exhaustive
  (M : ProFiltPseuNormGrpWithTinv₁ r) (x : Λ →+ M) :
  ∃ c : ℝ≥0, x ∈ pseudo_normed_group.filtration (Λ →+ M) c :=
begin
  obtain ⟨ι,hι,l,hl,h⟩ := polyhedral_lattice.polyhedral Λ,
  resetI,
  let cs : ι → ℝ≥0 := λ i, (M.exhaustive r (x (l i))).some,
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
  apply (M.exhaustive r (x (l i))).some_spec,
end
-/

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

def hom_functor'_cone_iso_hom :
  bounded_cone_point (Ab.limit_cone' ((K ⋙ hom_functor' Λ) ⋙ _)) ⟶
  (hom_functor' Λ).obj (bounded_cone_point (Ab.limit_cone' (K ⋙ _))) :=
{ to_fun := λ f,
  { to_fun := λ q,
    { val :=
      { val := λ j, (f.1.1 j).1 q,
        property := begin
          intros i j g,
          let h := f.1.2,
          specialize h g,
          dsimp at h ⊢,
          rw ← h,
          refl,
        end },
      property := begin
        obtain ⟨c,hc⟩ := f.2,
        -- we don't choose `c`, but rather a large enough `c'`
        -- taking into account some `m` generating the norm of `Λ`.
        sorry
      end },
    map_zero' := sorry,
    map_add' := sorry },
  map_zero' := sorry,
  map_add' := sorry,
  strict' := sorry }

def hom_functor'_cone_iso_inv :
  (hom_functor' Λ).obj (bounded_cone_point (Ab.limit_cone' (K ⋙ _))) ⟶
  bounded_cone_point (Ab.limit_cone' ((K ⋙ hom_functor' Λ) ⋙ _)) :=
{ to_fun := λ f,
  { val :=
    { val := λ j,
      { to_fun := λ q, (f.1 q).1.1 j,
        map_zero' := sorry,
        map_add' := sorry },
      property := sorry },
    property := sorry },
  map_zero' := sorry,
  map_add' := sorry,
  strict' := sorry }

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

def drop_Profinite_Tinv :
  ProFiltPseuNormGrpWithTinv₁ r ⥤ PseuNormGrp₁ :=
{ obj := λ M,
  { carrier := M,
    exhaustive' := M.exhaustive r },
  map := λ X Y f, { strict' := λ c x h, f.strict h .. f.to_add_monoid_hom } }

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

def drop_Profinite_drop_Tinv :
  ProFiltPseuNormGrpWithTinv₁.to_PFPNG₁ r ⋙ drop_Profinite ≅
  drop_Profinite_Tinv r :=
nat_iso.of_components (λ X, iso.refl _) $ by tidy

instance : preserves_limits (drop_Profinite_Tinv r) :=
preserves_limits_of_nat_iso (drop_Profinite_drop_Tinv r)

def hom_functor'_forget_iso (c) :
  drop_Profinite_Tinv r ⋙ hom_functor' Λ ⋙ PseuNormGrp₁.level.obj c ≅
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
  change preserves_limits (drop_Profinite_Tinv r ⋙ (hom_functor' Λ ⋙
    PseuNormGrp₁.level.obj c)),
  apply limits.comp_preserves_limits,
end


/- #########
-- This should be the functor sending `M` to `α → M`.
@[simps] def pi_functor (α : Type u) [fintype α] :
  ProFiltPseuNormGrpWithTinv₁.{u} r ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r :=
{ obj := λ M, ProFiltPseuNormGrpWithTinv₁.product r (λ i : α, M),
  map := λ M N f, ProFiltPseuNormGrpWithTinv₁.product.lift _ _ _ $
    λ i, ProFiltPseuNormGrpWithTinv₁.product.π _ _ i ≫ f } .

def hom_functor_forget_iso {α : Type u} [fintype α] (e : basis α ℤ Λ) :
  pi_functor r α ⋙ forget _ ≅ hom_functor r Λ ⋙ forget _ :=
nat_iso.of_components
(λ X,
  { hom := λ (f : α → X), (e.constr ℤ f).to_add_monoid_hom,
    inv := λ (f : Λ →+ X), (e.constr ℤ : (α → X) ≃ₗ[ℤ] _).symm f.to_int_linear_map,
    hom_inv_id' := by { ext1 f, exact (e.constr ℤ : (α → X) ≃ₗ[ℤ] _).symm_apply_apply f },
    inv_hom_id' := begin
      ext1 f,
      have := (e.constr ℤ : (α → X) ≃ₗ[ℤ] _).apply_symm_apply f.to_int_linear_map,
      convert congr_arg linear_map.to_add_monoid_hom this using 1,
      ext, refl,
    end })
begin
  intros M₁ M₂ f,
  ext x l,
  dsimp,
  simp only [basis.constr_apply_fintype, f.map_sum, map_zsmul],
  apply fintype.sum_congr,
  intro i,
  rw profinitely_filtered_pseudo_normed_group_with_Tinv_hom.map_zsmul,
  refl
end

/-

Hom(Λ, lim_i A_i)_{≤ c} should be "the same" as
lim_i Hom(Λ, A_i)_{≤ c}

I'm fairly sure this is correct, but this will be a bit of a challenge to prove...

Idea:

Since the forgetful functor on profinite creates limits, it suffices to prove this for the
underlying sets.

Now, choose a finite basis `e` for `Λ`, and a family `m : ι → Λ` generating the norm for `Λ`.
This gives us a map
`Hom(Λ,M) → (ι → M)`
given by composition with `m`.

Since `Λ` has a finite basis `e`, it follows that `Hom(Λ,-)` commutes with limits.
One might expect this to be true in general, but there is a subtlety in how limits are defined
in `ProFiltPseuNormGroupWithTinv₁`, as they are essentially of the form `colim_c (lim_i M_{i,c})`,
so one needs to use the fact that finite limits commute with filtered colimits to obtain this
(and this is where the finiteness of the basis is used).
Similarly, `ι` is finite, so that `(ι → M)` commutes with limits in the variable `M`.

Now we can identify `(ι → M)` with the categorical product in `ProFilt...₁`, and use the fact
that the functor `level.obj c` preserves limits to obtain the desired result.
-/

instance pi_functor_preserves_limits {α : Type u} [fintype α] :
  preserves_limits (pi_functor r α) :=
begin
  constructor, introsI J _, constructor, intros K, constructor, intros C hC,
  refine ⟨λ S, _,_,_⟩,
  { refine ProFiltPseuNormGrpWithTinv₁.product.lift _ _ _ _,
    intros i,
    refine hC.lift ⟨_,_,_⟩,
    { intros j,
      refine S.π.app _ ≫ ProFiltPseuNormGrpWithTinv₁.product.π _ _ i },
    { sorry } },
  { sorry },
  { sorry }
end

--instance hom_functor_forget_preserves_limits :
--preserves_limits (hom_functor r Λ ⋙ forget _) :=
--begin
--  -- Λ is finite free
--  let b := module.free.choose_basis ℤ Λ,
--  let e : (pi_functor r _ ⋙ forget _) ≅ (hom_functor r Λ ⋙ forget _) :=
--    (hom_functor_forget_iso r Λ b),
--  apply preserves_limits_of_nat_iso e,
--end

-- NOTE: `polyhedral_lattice.polyhedral` uses `ι : Type` instead of a universe polymorphic variant.
-- We mimic `ι : Type` here...
def hom_functor_level_forget_aux {ι : Type} [fintype ι] (m : ι → Λ)
  (hm : generates_norm m) (c : ℝ≥0) :
  ProFiltPseuNormGrpWithTinv₁.{u} r ⥤ Type u :=
{ obj := λ M,
    { f : Λ →+ M | ∀ i : ι, f (m i) ∈ pseudo_normed_group.filtration M (c * ∥ m i ∥₊) },
  map := λ M N f t, ⟨f.to_add_monoid_hom.comp t, λ i, f.strict (t.2 i)⟩,
  map_id' := λ M, by { ext, refl },
  map_comp' := by { intros, ext, refl } }

def hom_functor_level_forget_aux_incl {ι : Type} [fintype ι] (m : ι → Λ)
  (hm : generates_norm m) (c : ℝ≥0) :
  hom_functor_level_forget_aux r Λ m hm c ⟶ hom_functor r Λ ⋙ forget _:=
{ app := λ X t, t.1,
  naturality' := λ M N f, by { ext, refl } }

-- Easy, use `mem_filtration_iff_of_is_limit` from the other file.
lemma mem_filtration_iff_of_is_limit {J : Type u}
  [small_category J] {ι : Type} [fintype ι]
  {K : J ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r}
  (m : ι → Λ)
  (hm : generates_norm m) (c : ℝ≥0)
  (C : cone K) (hC : is_limit C) (f : Λ →+ C.X) (i : ι) :
  f (m i) ∈ pseudo_normed_group.filtration C.X c ↔
  (∀ (j : J), (C.π.app j) (f (m i)) ∈
    pseudo_normed_group.filtration (K.obj j) (c * ∥ m i ∥₊)) := sorry

def hom_functor_level_forget_aux_cone_is_limit {J : Type u}
  [small_category J] {ι : Type} [fintype ι]
  {K : J ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r}
  (m : ι → Λ)
  (B : Type u)
  [fintype B]
  (e : basis B ℤ Λ)
  (hm : generates_norm m)
  (c : ℝ≥0)
  (C : cone K) (hC : is_limit C) :
  is_limit ((hom_functor_level_forget_aux r Λ m hm c).map_cone C) :=
sorry

-- This instance can probably be proved by hand.
instance hom_functor_level_forget_aux_preserves_limits {ι : Type} [fintype ι] (m : ι → Λ)
  (hm : generates_norm m) (c : ℝ≥0) :
  preserves_limits (hom_functor_level_forget_aux r Λ m hm c) :=
begin
  sorry
  /-
  constructor, introsI J hJ, constructor, intros K, constructor, intros C hC,
  let ι := module.free.choose_basis_index ℤ Λ,
  let ℬ : basis ι _ _ := module.free.choose_basis ℤ Λ,
  let C' := (pi_functor r ι).map_cone C,
  let hC' : is_limit C' := is_limit_of_preserves (pi_functor r ι) hC,
  let η : K ⋙ pi_functor r ι ⋙ forget _ ≅ K ⋙ hom_functor r Λ ⋙ forget _ :=
    iso_whisker_left _ (hom_functor_forget_iso r Λ ℬ),
  let γ : K ⋙ hom_functor_level_forget_aux r Λ m hm c ⟶ K ⋙ (hom_functor r Λ ⋙ forget _) :=
      whisker_left _ (hom_functor_level_forget_aux_incl r Λ m hm c),
  let δ := γ ≫ η.inv,

  refine ⟨λ S, _, _, _⟩,

  { sorry },

  { sorry },

  { sorry }
  -/

  /-
  -- `Hom(Λ,C.X)` is the limit of of `Hom(Λ,K.obj j)`.
  let hC' := is_limit_of_preserves (hom_functor r Λ ⋙ forget _) hC,
  -- `C.X_{≤ c}` is the limit of of `(K.obj j)_{≤ c}`, when considered as sets.
  let hC'' :=
    is_limit_of_preserves (ProFiltPseuNormGrpWithTinv₁.to_PFPNG₁ r) hC,
  let η : K ⋙ hom_functor_level_forget_aux r Λ m hm c ⟶
      K ⋙ (hom_functor r Λ ⋙ forget _) :=
      whisker_left _ (hom_functor_level_forget_aux_incl r Λ m hm c),
  have key : ∀ S (j : J) x (q : Λ),
    (C.π.app j) ((hC'.lift ((cones.postcompose η).obj S) x : Λ →+ _).to_fun q) =
    (S.π.app j x).val q,
  { intros S j x q,
    have := hC'.fac ((cones.postcompose η).obj S) j,
    dsimp [hom_functor_level_forget_aux_incl] at this,
    apply_fun (λ e, e x q) at this,
    dsimp at this,
    erw ← this,
    refl },
  refine ⟨λ S, _, _, _⟩,
  { let T := (cones.postcompose η).obj S,
    let t := hC'.lift T,
    refine (λ x, ⟨t x, _⟩),
    intros i,
    let tt := t x,
    dsimp at tt,
    erw ProFiltPseuNormGrp₁.mem_filtration_iff_of_is_limit _ _ hC'',
    intros j,
    change (C.π.app j) _ ∈ pseudo_normed_group.filtration (K.obj j) _,
    have hx := (S.π.app j x).2 i,
    convert hx,
    apply key },
  { intros S j,
    ext x q : 3,
    apply key },
  { intros S w hw,
    ext x q : 3,
    dsimp,
    apply ProFiltPseuNormGrpWithTinv₁.is_limit_ext r _ _ hC,
    intros j,
    erw key,
    rw ← hw,
    refl }
  -/
end

-- This is more-or-less by definition!
-- TODO: The definition of this nat_iso can be broken up a bit.
-- for example, the isomorphism of the individual types is essentially just
-- and equivalence of subtypes defined by equivalent predicates. I'm sure
-- we have some general equivalence we can use here, but one would still
-- have to convert a type equivalence to an isomoprhism in the category `Type u`.
def hom_functor_level_forget_iso {ι : Type} [fintype ι] (m : ι → Λ)
  (hm : generates_norm m) (c : ℝ≥0) :
  hom_functor_level_forget_aux r Λ m hm c ≅
  hom_functor r Λ ⋙
  ProFiltPseuNormGrpWithTinv₁.to_PFPNG₁ r ⋙
  ProFiltPseuNormGrp₁.level.obj c ⋙
  forget _ :=
nat_iso.of_components (λ M,
{ hom := λ t, ⟨t.1, begin
    erw generates_norm.add_monoid_hom_mem_filtration_iff hm,
    intros i,
    apply t.2,
  end⟩,
  inv := λ t, ⟨t.1, begin
    dsimp,
    erw ← generates_norm.add_monoid_hom_mem_filtration_iff hm,
    exact t.2,
  end⟩,
  hom_inv_id' := by { ext, refl },
  inv_hom_id' := by { ext, refl } }) $ by { intros, ext, refl }

instance hom_functor_level_forget_preserves_limits (c) : preserves_limits (
  hom_functor r Λ ⋙
  ProFiltPseuNormGrpWithTinv₁.to_PFPNG₁ r ⋙
  ProFiltPseuNormGrp₁.level.obj c ⋙
  forget _ ) :=
begin
  choose ι hι m hm h using polyhedral_lattice.polyhedral Λ,
  resetI,
  apply preserves_limits_of_nat_iso (hom_functor_level_forget_iso r Λ m hm c),
end
####### -/

end

/-- Lemma 9.8 of [Analytic] -/
lemma lem98 (r' : ℝ≥0) [fact (0 < r')] [fact (r' < 1)]
  (Λ : Type*) [polyhedral_lattice Λ] (S : Profinite) (N : ℕ) [hN : fact (0 < N)] :
  pseudo_normed_group.splittable (Λ →+ (Mbar.functor r').obj S) N (lem98.d Λ N) :=
begin
  -- This reduces to `lem98_finite`: See the first lines of the proof in [Analytic].
  sorry
end
