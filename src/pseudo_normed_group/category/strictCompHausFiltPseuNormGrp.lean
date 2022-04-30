import pseudo_normed_group.category.CompHausFiltPseuNormGrp

universe variables u

open category_theory
open_locale nnreal

local attribute [instance] type_pow

noncomputable theory

/-- The category of CompHaus-ly filtered pseudo-normed groups with exhaustive filtrations
and with strict morphisms. -/
structure CompHausFiltPseuNormGrp₁ : Type (u+1) :=
(M : Type u)
[str : comphaus_filtered_pseudo_normed_group M]
(exhaustive' : ∀ m : M, ∃ c, m ∈ pseudo_normed_group.filtration M c)

namespace CompHausFiltPseuNormGrp₁

instance : has_coe_to_sort CompHausFiltPseuNormGrp₁ Type* := ⟨λ M, M.M⟩
instance (M : CompHausFiltPseuNormGrp₁) : comphaus_filtered_pseudo_normed_group M := M.str

lemma exhaustive (M : CompHausFiltPseuNormGrp₁) (m : M) :
  ∃ c, m ∈ pseudo_normed_group.filtration M c := M.exhaustive' _

instance : large_category CompHausFiltPseuNormGrp₁.{u} :=
{ hom := λ A B, strict_comphaus_filtered_pseudo_normed_group_hom A B,
  id := λ A, strict_comphaus_filtered_pseudo_normed_group_hom.id,
  comp := λ A B C f g, g.comp f }

/-- The "forget ₁" functor from `CompHaus`-ly filtered normed groups with strict morphisms,
  to CompHaus-ly filtered pseudo-normed groups with bounded morphisms, which is the
  identity on objects. -/
@[simps]
def _root_.CHFPNG₁_to_CHFPNGₗₑ : CompHausFiltPseuNormGrp₁ ⥤ CompHausFiltPseuNormGrp :=
{ obj := λ M, CompHausFiltPseuNormGrp.of M,
  map := λ M₁ M₂ f, f.to_chfpsng_hom }

instance : faithful (CHFPNG₁_to_CHFPNGₗₑ.{u}) :=
{ map_injective' := λ M₁ M₂ f g h,
  by { ext x, apply_fun (λ φ, φ.to_fun) at h, exact congr_fun h x } }

instance : concrete_category CompHausFiltPseuNormGrp₁.{u} :=
{ forget :=
  { obj := λ M, M.M,
    map := λ A B f, f },
  forget_faithful := ⟨⟩ } .

def level : ℝ≥0 ⥤ CompHausFiltPseuNormGrp₁.{u} ⥤ CompHaus :=
{ obj := λ c,
  { obj := λ M, CompHaus.of $ pseudo_normed_group.filtration M c,
    map := λ A B f, ⟨_, f.level_continuous _⟩ },
  map := λ c₁ c₂ h,
    { app := λ M, by letI : fact (c₁ ≤ c₂) := ⟨le_of_hom h⟩; exact
        ⟨_, comphaus_filtered_pseudo_normed_group.continuous_cast_le _ _⟩ } } .

section limits

/-!
In this section, we show (hopefully ;)) that `CompHausFiltPseuNormGrp₁` has limits.
-/

variables {J : Type u} [small_category J] (G : J ⥤ CompHausFiltPseuNormGrp₁.{u})

open pseudo_normed_group
open category_theory.limits

/-- This is a bifunctor which associates to each `c : ℝ≥0` and `j : J`,
  the `c`-th term of the filtration of `G.obj j`. -/
def cone_point_diagram : as_small.{u} ℝ≥0 ⥤ J ⥤ CompHaus.{u} :=
as_small.down ⋙ level ⋙ (whiskering_left _ _ _).obj G

@[derive [topological_space, t2_space]]
def cone_point_type_filt (c : ℝ≥0) : Type u :=
{ x : Π j : J, filtration (G.obj j) c | ∀ ⦃i j : J⦄ (e : i ⟶ j), (G.map e).level (x _) = x _ }

instance (c : ℝ≥0) : compact_space (cone_point_type_filt G c) :=
(CompHaus.limit_cone (((cone_point_diagram G).obj (as_small.up.obj c)))).X.is_compact -- ;-)

namespace cone_point_type_filt

variable {G}

instance (c : ℝ≥0) : has_coe_to_fun (cone_point_type_filt G c)
  (λ x, Π j : J, filtration (G.obj j) c) := ⟨λ x, x.1⟩

@[ext] lemma ext {c} (x y : cone_point_type_filt G c) :
  (⇑x : Π j : J, filtration (G.obj j) c) = y → x = y := subtype.ext

@[simp] lemma level_apply {c : ℝ≥0} {i j : J} (x : cone_point_type_filt G c) (e : i ⟶ j) :
  (G.map e).level (x i) = x j := x.2 e

@[simp] lemma map_apply {c : ℝ≥0} {i j : J} (x : cone_point_type_filt G c) (e : i ⟶ j) :
  (G.map e) (x i) = x j := by {rw ← (G.map e).coe_level, simp }

def trans {c₁ c₂ : ℝ≥0} (h : c₁ ≤ c₂) (x : cone_point_type_filt G c₁) : cone_point_type_filt G c₂ :=
⟨λ j, cast_le' h (x j), λ i j e, by { ext, simp }⟩

@[simp] lemma trans_apply {c₁ c₂ : ℝ≥0} (h : c₁ ≤ c₂) (x : cone_point_type_filt G c₁) (j : J) :
  x.trans h j = cast_le' h (x j) := by { ext, refl }

lemma trans_injective {c₁ c₂ : ℝ≥0} (h : c₁ ≤ c₂) :
  function.injective (trans h : cone_point_type_filt G c₁ → cone_point_type_filt G c₂) :=
begin
  intros x y hh,
  ext j,
  apply_fun (λ e, (e j : G.obj j)) at hh,
  exact hh
end

lemma trans_continuous {c₁ c₂ : ℝ≥0} (h : c₁ ≤ c₂) :
  continuous (trans h : cone_point_type_filt G c₁ → cone_point_type_filt G c₂) :=
begin
  -- ;-)
  let η := ((cone_point_diagram G).map (as_small.up.map $ hom_of_le $ h)),
  let hS := (CompHaus.limit_cone_is_limit (((cone_point_diagram G).obj (as_small.up.obj c₂)))),
  let T := (CompHaus.limit_cone (((cone_point_diagram G).obj (as_small.up.obj c₁)))),
  exact (hS.map T η).continuous,
end

lemma continuous_apply {c : ℝ≥0} (j : J) : continuous (λ t : cone_point_type_filt G c, t j) :=
begin
  change continuous ((λ u : Π j, filtration (G.obj j) c, u j) ∘
    (λ u : cone_point_type_filt G c, ⇑u)),
  apply continuous.comp,
  apply continuous_apply,
  apply continuous_subtype_coe,
end

instance {c} : has_zero (cone_point_type_filt G c) := has_zero.mk $
⟨λ j, 0, λ i j e, by { ext, dsimp, simp }⟩

instance {c} : has_neg (cone_point_type_filt G c) := has_neg.mk $ λ x,
⟨λ j, - (x j), λ i j e, by { ext, dsimp, simp, }⟩

def add' {c₁ c₂} (x : cone_point_type_filt G c₁) (y : cone_point_type_filt G c₂) :
  cone_point_type_filt G (c₁ + c₂) :=
⟨λ j, add' (x j, y j), λ i j e, by { ext, dsimp, simp, }⟩

@[simp] lemma zero_apply {c} (j : J) : (0 : cone_point_type_filt G c) j = 0 := rfl
@[simp] lemma neg_apply {c} (j : J) (x : cone_point_type_filt G c) : (-x) j = - (x j) := rfl
@[simp] lemma add'_apply_coe {c₁ c₂} (j : J) (x : cone_point_type_filt G c₁)
  (y : cone_point_type_filt G c₂) : ((x.add' y) j : G.obj j) = x j + y j := rfl

lemma continuous_neg {c} : continuous (λ x : cone_point_type_filt G c, - x) :=
begin
  apply continuous_subtype_mk,
  apply continuous_pi,
  intros j,
  change continuous ((λ x, -x) ∘ (λ a : cone_point_type_filt G c, (a j))),
  apply continuous.comp,
  apply comphaus_filtered_pseudo_normed_group.continuous_neg',
  apply continuous_apply,
end

lemma continuous_add' {c1 c2} :
  continuous (λ t : cone_point_type_filt G c1 × cone_point_type_filt G c2, t.1.add' t.2) :=
begin
  apply continuous_subtype_mk,
  apply continuous_pi,
  intros j,
  let A : cone_point_type_filt G c1 × cone_point_type_filt G c2 →
    (Π j : J, filtration (G.obj j) c1) × (Π j : J, filtration (G.obj j) c2) :=
    λ t, (t.1,t.2),
  let B : (Π j : J, filtration (G.obj j) c1) × (Π j : J, filtration (G.obj j) c2) →
    filtration (G.obj j) c1 × filtration (G.obj j) c2 := λ t, (t.1 j, t.2 j),
  let C : filtration (G.obj j) c1 × filtration (G.obj j) c2 → filtration (G.obj j) (c1 + c2) :=
    pseudo_normed_group.add',
  change continuous (C ∘ B ∘ A),
  apply continuous.comp,
  apply comphaus_filtered_pseudo_normed_group.continuous_add',
  apply continuous.comp,
  { apply continuous.prod_mk,
    { change continuous ((λ t : Π j : J, filtration (G.obj j) c1, t j) ∘ prod.fst),
      apply continuous.comp,
      apply _root_.continuous_apply,
      exact continuous_fst },
    { change continuous ((λ t : Π j : J, filtration (G.obj j) c2, t j) ∘ prod.snd),
      apply continuous.comp,
      apply _root_.continuous_apply,
      exact continuous_snd } },
  apply continuous.prod_map,
  apply continuous_subtype_coe,
  apply continuous_subtype_coe,
end

end cone_point_type_filt

def cone_point_type_setoid : setoid (Σ (c : ℝ≥0), cone_point_type_filt G c) :=
{ r := λ x y, ∃ (d : ℝ≥0) (hx : x.1 ≤ d) (hy : y.1 ≤ d), x.2.trans hx = y.2.trans hy,
  iseqv := begin
    refine ⟨_,_,_⟩,
    { rintro ⟨c,x⟩,
      use [c, le_refl _, le_refl _] },
    { rintro ⟨c,x⟩ ⟨d,y⟩ ⟨e,h1,h2,h⟩,
      dsimp at *,
      refine ⟨_, le_sup_left, le_sup_right, _⟩,
      ext j : 3,
      symmetry,
      apply_fun (λ e, (e j : G.obj j)) at h,
      exact h },
    { rintro ⟨c,x⟩ ⟨d,y⟩ ⟨e,z⟩ ⟨i,h1,hh1,hhh1⟩ ⟨j,h2,hh2,hhh2⟩,
      dsimp at *,
      refine ⟨_, le_sup_left, le_sup_right, _⟩,
      ext jj : 3,
      apply_fun (λ e, (e jj : G.obj jj)) at hhh1,
      apply_fun (λ e, (e jj : G.obj jj)) at hhh2,
      erw [hhh1, hhh2], refl },
  end }

def cone_point_type : Type u := quotient (cone_point_type_setoid G)

namespace cone_point_type
variable {G}

def incl (c : ℝ≥0) : cone_point_type_filt G c → cone_point_type G :=
quotient.mk' ∘ sigma.mk c

lemma incl_injective (c : ℝ≥0) :
  function.injective (incl c : cone_point_type_filt G c → cone_point_type G) :=
begin
  intros x y h,
  replace h := quotient.exact' h,
  obtain ⟨d,h1,h2,h⟩ := h,
  dsimp at h1 h2 h,
  rw (show h1 = h2, by refl) at h,
  apply cone_point_type_filt.trans_injective h2,
  exact h,
end

@[simp]
lemma incl_trans {c₁ c₂ : ℝ≥0} (h : c₁ ≤ c₂) (x : cone_point_type_filt G c₁) :
  incl _ (x.trans h) = incl _ x :=
begin
  apply quotient.sound',
  refine ⟨c₁ ⊔ c₂, by simp, by simp, _⟩,
  ext,
  refl,
end

lemma incl_jointly_surjective (x : cone_point_type G) :
  ∃ (c : ℝ≥0) (y : cone_point_type_filt G c), incl c y = x :=
begin
  rcases x,
  obtain ⟨c,y⟩ := x,
  use [c,y],
  refl,
end

def index (x : cone_point_type G) : ℝ≥0 := (incl_jointly_surjective x).some

def preimage (x : cone_point_type G) : cone_point_type_filt G x.index :=
  (incl_jointly_surjective x).some_spec.some

@[simp]
lemma preimage_spec (x : cone_point_type G) : incl _ x.preimage = x :=
  (incl_jointly_surjective x).some_spec.some_spec

@[simp]
lemma coe_incl_preimage_apply {c} (x : cone_point_type_filt G c) (j : J) :
  ((incl c x).preimage j : G.obj j) = x j :=
begin
  let e := c ⊔ (incl c x).index,
  change _ = (cast_le' le_sup_left (x j) : G.obj j),
  rw ← cone_point_type_filt.trans_apply (le_sup_left : _ ≤ e) x j,
  rw ← coe_cast_le' (le_sup_right : _ ≤ e),
  rw ← cone_point_type_filt.trans_apply,
  congr' 2,
  apply incl_injective,
  simp,
end


instance : has_zero (cone_point_type G) := ⟨incl 0 0⟩

lemma zero_def : (0 : cone_point_type G) = incl 0 0 := rfl

instance : has_neg (cone_point_type G) := has_neg.mk $
λ x, incl _ (-x.preimage)

lemma neg_def (x : cone_point_type G) : -x = incl _ (-x.preimage) := rfl

instance : has_add (cone_point_type G) := has_add.mk $
λ x y, incl _ (x.preimage.add' y.preimage)

lemma add_def (x y : cone_point_type G) : x + y = incl _ (x.preimage.add' y.preimage) := rfl

lemma incl_add_incl (c₁ c₂ : ℝ≥0)
  (x₁ : cone_point_type_filt G c₁) (x₂ : cone_point_type_filt G c₂) :
  (incl c₁ x₁) + (incl c₂ x₂) = (incl (c₁ + c₂) (x₁.add' x₂)) :=
begin
  rw add_def,
  apply quotient.sound',
  refine ⟨max _ _, le_max_left _ _, le_max_right _ _, _⟩,
  ext,
  simp only [cone_point_type_filt.trans_apply, cone_point_type_filt.add'_apply_coe,
    coe_cast_le, coe_incl_preimage_apply, coe_cast_le'],
end

lemma zero_add (x : cone_point_type G) : 0 + x = x :=
begin
  conv_rhs {rw ← x.preimage_spec},
  apply quotient.sound',
  refine ⟨(0 : cone_point_type G).index + x.index, by simp, by simp, _⟩,
  dsimp,
  ext j : 3,
  simp only [cone_point_type_filt.trans_apply, cone_point_type_filt.add'_apply_coe, coe_cast_le'],
  simp only [add_left_eq_self],
  apply coe_incl_preimage_apply,
end

lemma add_comm (x y : cone_point_type G) : x + y = y + x :=
begin
  apply quotient.sound',
  refine ⟨x.index + y.index, le_refl _, le_of_eq (by {dsimp, rw add_comm}), _⟩,
  dsimp,
  ext j : 3,
  simp only [cone_point_type_filt.trans_apply, cone_point_type_filt.add'_apply_coe,
    coe_cast_le, coe_cast_le'],
  rw add_comm,
end

lemma add_zero (x : cone_point_type G) : x + 0 = x := by { rw add_comm, apply zero_add }

lemma add_assoc (x y z : cone_point_type G) : x + y + z = x + (y + z) :=
begin
  apply quotient.sound',
  refine ⟨_, le_sup_left, le_sup_right, _⟩,
  dsimp,
  ext j : 3,
  simp only [cone_point_type_filt.trans_apply, cone_point_type_filt.add'_apply_coe,
    coe_cast_le, coe_cast_le'],
  erw [coe_incl_preimage_apply, coe_incl_preimage_apply],
  simp [add_assoc],
end

lemma add_left_neg (x : cone_point_type G) : -x + x = 0 :=
begin
  apply quotient.sound',
  refine ⟨_,le_sup_left, le_sup_right,_⟩,
  dsimp,
  ext j : 3,
  simp only [cone_point_type_filt.trans_apply, cone_point_type_filt.zero_apply,
    cone_point_type_filt.add'_apply_coe, coe_cast_le, filtration.coe_zero, coe_cast_le'],
  erw coe_incl_preimage_apply,
  simp,
end

instance : add_comm_group (cone_point_type G) :=
{ add_assoc := add_assoc,
  zero_add := zero_add,
  add_zero := add_zero,
  add_left_neg := add_left_neg,
  add_comm := add_comm,
  ..(infer_instance : has_add _),
  ..(infer_instance : has_zero _),
  ..(infer_instance : has_neg _) }

variable (G)
def filt (c : ℝ≥0) : set (cone_point_type G) := set.range (incl c)

def filt_equiv (c : ℝ≥0) : cone_point_type_filt G c ≃ filt G c :=
equiv.of_bijective (λ x, ⟨_, x, rfl⟩)
begin
  split,
  { intros x y h,
    apply_fun (λ e, e.val) at h,
    apply incl_injective,
    exact h },
  { rintro ⟨_,x,rfl⟩, use x }
end

instance {c} : topological_space (filt G c) :=
topological_space.induced (filt_equiv G c).symm infer_instance

def filt_homeo (c : ℝ≥0) : filt G c ≃ₜ cone_point_type_filt G c :=
homeomorph.homeomorph_of_continuous_open (filt_equiv G c).symm continuous_induced_dom
begin
  intros U hU,
  have : inducing (filt_equiv G c).symm := ⟨rfl⟩,
  rw this.is_open_iff at hU,
  obtain ⟨U,hU,rfl⟩ := hU,
  simpa,
end

instance {c} : compact_space (filt G c) :=
(filt_homeo G c).symm.compact_space

instance {c} : t2_space (filt G c) :=
(filt_homeo G c).symm.t2_space

def filt_iso (c : ℝ≥0) : CompHaus.of (filt G c) ≅
  (CompHaus.limit_cone (((cone_point_diagram G).obj (as_small.up.obj c)))).X :=
{ hom := (filt_homeo G c).to_continuous_map,
  inv := (filt_homeo G c).symm.to_continuous_map,
  hom_inv_id' := by { ext1, simp },
  inv_hom_id' := by { ext1, simp } }

variable {G}

@[simp] lemma incl_neg {c} (x : cone_point_type_filt G c) :
  incl c (-x) = - incl c x :=
begin
  apply quotient.sound',
  refine ⟨_, le_sup_left, le_sup_right, _⟩,
  dsimp,
  ext j : 3,
  simp,
end

@[simp] lemma incl_add' {c1 c2} (x1 : cone_point_type_filt G c1) (x2 : cone_point_type_filt G c2) :
  incl (c1 + c2) (x1.add' x2) = incl c1 x1 + incl c2 x2 :=
begin
  apply quotient.sound',
  refine ⟨_, le_sup_left, le_sup_right, _⟩,
  dsimp,
  ext j : 3,
  simp,
end

@[simp] lemma incl_zero {c} : incl c (0 : cone_point_type_filt G c) = 0 :=
begin
  apply quotient.sound',
  refine ⟨_, le_sup_left, le_sup_right, _⟩,
  dsimp,
  ext j : 3,
  simp,
end

instance : pseudo_normed_group (cone_point_type G) :=
{ filtration := filt G,
  filtration_mono := begin
    rintro c1 c2 h x ⟨x,rfl⟩,
    dsimp [filt],
    use x.trans h,
    simp,
  end,
  zero_mem_filtration := begin
    intro c,
    use 0,
    simp,
  end,
  neg_mem_filtration := begin
    rintros c x ⟨x,rfl⟩,
    use -x,
    simp,
  end,
  add_mem_filtration := begin
    rintros c1 c2 x1 x2 ⟨x1,rfl⟩ ⟨x2,rfl⟩,
    use x1.add' x2,
    simp,
  end }

instance : comphaus_filtered_pseudo_normed_group (cone_point_type G) :=
{ topology := by apply_instance,
  t2 := by apply_instance,
  compact := by apply_instance,
  continuous_add' := begin
    intros c1 c2,
    let E : filtration (cone_point_type G) c1 × filtration (cone_point_type G) c2 →
      cone_point_type_filt G c1 × cone_point_type_filt G c2 :=
      λ t, ⟨(filt_homeo G c1) t.1, (filt_homeo G c2) t.2⟩,
    let E' : cone_point_type_filt G c1 × cone_point_type_filt G c2 →
      filtration (cone_point_type G) c1 × filtration (cone_point_type G) c2 :=
      λ t, ⟨(filt_homeo G c1).symm t.1, (filt_homeo G c2).symm t.2⟩,
    have hE'E : E' ∘ E = id := by { dsimp [E,E'], ext, simp, simp },
    have : (filt_homeo G (c1 + c2)).symm ∘
      (λ t : cone_point_type_filt G c1 × cone_point_type_filt G c2, t.1.add' t.2) ∘ E = add',
    { suffices : add' ∘ E' = (filt_homeo G (c1 + c2)).to_equiv.symm ∘
        (λ t : cone_point_type_filt G c1 × cone_point_type_filt G c2, t.1.add' t.2),
      { erw [← function.comp.assoc, ← this, function.comp.assoc, hE'E],
        simp },
      dsimp only [filt_homeo, homeomorph.homeomorph_of_continuous_open, E'],
      ext,
      dsimp [filt_homeo, filt_equiv, E, E'],
      simp },
    rw ← this, clear this,
    apply continuous.comp (homeomorph.continuous _),
    apply continuous.comp,
    apply cone_point_type_filt.continuous_add',
    dsimp [E],
    continuity,
  end,
  continuous_neg' := begin
    intros c,
    have : (neg' : filtration (cone_point_type G) c → filtration (cone_point_type G) c) =
      (filt_homeo G c).symm ∘ (λ x, -x) ∘ filt_homeo G c,
    { suffices :
        (neg' : filtration (cone_point_type G) c → filtration (cone_point_type G) c) ∘
          (filt_homeo G c).to_equiv.symm = (filt_homeo G c).to_equiv.symm ∘ (λ x, -x),
      { erw [← function.comp.assoc, ← this, function.comp.assoc, equiv.symm_comp_self],
        simp },
      dsimp only [filt_homeo, homeomorph.homeomorph_of_continuous_open],
      simp only [equiv.symm_symm],
      ext,
      dsimp [filt_equiv],
      simp },
    rw this,
    simp [cone_point_type_filt.continuous_neg],
  end,
  continuous_cast_le := begin
    rintro c₁ c₂ ⟨h⟩,
    change continuous (cast_le' h),
    have : cast_le' h = (filt_homeo G c₂).symm ∘
      cone_point_type_filt.trans h ∘ (filt_homeo G c₁),
    { suffices : cast_le' h ∘ (filt_homeo G c₁).to_equiv.symm =
        (filt_homeo G c₂).to_equiv.symm ∘ cone_point_type_filt.trans h,
      { erw [← function.comp.assoc, ← this, function.comp.assoc, equiv.symm_comp_self],
        simp },
      dsimp only [filt_homeo, homeomorph.homeomorph_of_continuous_open],
      simp only [equiv.symm_symm],
      ext,
      dsimp [filt_equiv],
      simp },
    simp [this, cone_point_type_filt.trans_continuous],
  end }

end cone_point_type

def cone_point : CompHausFiltPseuNormGrp₁ :=
{ M := cone_point_type G,
  exhaustive' := cone_point_type.incl_jointly_surjective }

def proj (j : J) : cone_point G ⟶ G.obj j :=
{ to_fun := λ x, x.preimage j,
  map_zero' := begin
    rw cone_point_type.zero_def,
    simp only [cone_point_type.coe_incl_preimage_apply,
      cone_point_type_filt.zero_apply, filtration.coe_zero],
  end,
  map_add' := begin
    intros x y,
    rw cone_point_type.add_def x y,
    simp only [cone_point_type.coe_incl_preimage_apply,
      cone_point_type_filt.add'_apply_coe],
  end,
  strict' := begin
    rintros c x ⟨x,rfl⟩,
    simp only [cone_point_type.coe_incl_preimage_apply,
      subtype.coe_prop],
  end,
  continuous' := begin
    intros c,
    dsimp,
    let E : filtration (cone_point_type G) c → filtration (G.obj j) c :=
      λ t, ((cone_point_type.filt_homeo G c) t) j,
    suffices : continuous E,
    { convert this,
      ext ⟨t,t,rfl⟩,
      dsimp [E],
      simp only [cone_point_type.coe_incl_preimage_apply],
      congr' 2,
      apply_fun (cone_point_type.filt_homeo G c).symm,
      simp only [homeomorph.symm_apply_apply],
      ext, refl },
    dsimp [E],
    change continuous ((λ (u : cone_point_type_filt G c), u j) ∘ cone_point_type.filt_homeo G c),
    simp only [homeomorph.comp_continuous_iff'],
    apply cone_point_type_filt.continuous_apply,
  end } .

def limit_cone : cone G :=
{ X := cone_point G,
  π :=
  { app := λ j, proj G j,
    naturality' := begin
      intros i j e,
      ext,
      dsimp,
      simp only [comp_apply, category.id_comp],
      have := (cone_point_type.preimage x).2 e,
      apply_fun (λ e, (e : G.obj j)) at this,
      exact this.symm,
    end } }

def index {M : CompHausFiltPseuNormGrp₁} (x : M) : ℝ≥0 := (M.exhaustive x).some
def preimage {M : CompHausFiltPseuNormGrp₁} (x : M) : filtration M (index x) :=
  ⟨x,(M.exhaustive x).some_spec⟩

def limit_cone_lift_map (D : cone G) : D.X → cone_point G := λ x,
cone_point_type.incl (index x) ⟨λ j, (D.π.app j).level (preimage x), begin
  intros i j e,
  ext,
  dsimp,
  simp,
end⟩

lemma limit_cone_lift_map_map_zero {D : cone G} :
  limit_cone_lift_map G D 0 = 0 :=
begin
  apply quotient.sound',
  refine ⟨_, le_sup_left, le_sup_right, _⟩,
  dsimp,
  ext j,
  simp only [cone_point_type_filt.trans_apply, cone_point_type_filt.zero_apply,
    coe_cast_le, filtration.coe_zero, coe_cast_le'],
  apply (D.π.app j).map_zero,
end

lemma limit_cone_lift_map_map_add {D : cone G} (a b : D.X) :
  limit_cone_lift_map G D (a + b) = limit_cone_lift_map G D a + limit_cone_lift_map G D b :=
begin
  apply quotient.sound',
  refine ⟨_, le_sup_left, le_sup_right, _⟩,
  dsimp,
  ext j,
  dsimp [limit_cone_lift_map],
  simp only [cone_point_type_filt.trans_apply, cone_point_type.coe_incl_preimage_apply,
    cone_point_type_filt.add'_apply_coe, coe_cast_le, coe_cast_le'],
  exact (D.π.app j).map_add a b,
end

lemma limit_cone_lift_map_strict {D : cone G} {x : D.X} (c : ℝ≥0) (hx : x ∈ filtration D.X c) :
  limit_cone_lift_map G D x ∈ filtration (cone_point_type G) c :=
begin
  dsimp [limit_cone_lift_map],
  change _ ∈ set.range _,
  refine ⟨⟨λ j, (D.π.app j).level ⟨x,hx⟩, _⟩, _⟩,
  { intros i j e,
    ext,
    dsimp,
    simp },
  { dsimp,
    apply quotient.sound',
    refine ⟨_, le_sup_left, le_sup_right, _⟩,
    dsimp,
    ext j,
    simpa }
end

def limit_cone_lift (D : cone G) : D.X ⟶ cone_point G :=
{ to_fun := limit_cone_lift_map _ D,
  map_zero' := limit_cone_lift_map_map_zero _,
  map_add' := limit_cone_lift_map_map_add _,
  strict' := λ c x hx, limit_cone_lift_map_strict G c hx,
  continuous' := begin
    intros c,
    rw (cone_point_type.filt_homeo G c).inducing.continuous_iff,
    let E : filtration D.X c → cone_point_type_filt G c := λ t,
      ⟨λ j, (D.π.app j).level t, _⟩,
    swap, {
      intros i j e,
      ext,
      dsimp,
      simp },
    have : (cone_point_type.filt_homeo G c) ∘ pseudo_normed_group.level
      (limit_cone_lift_map G D) (λ c x hx, limit_cone_lift_map_strict G c hx) c = E,
    { ext1,
      apply_fun (cone_point_type.filt_homeo G c).symm,
      dsimp [E],
      simp only [homeomorph.symm_apply_apply],
      ext,
      apply quotient.sound',
      refine ⟨_, le_sup_left, le_sup_right, _⟩,
      ext,
      dsimp,
      simp only [cone_point_type_filt.trans_apply, coe_cast_le, coe_cast_le'],
      refl },
    rw this,
    apply continuous_subtype_mk,
    apply continuous_pi,
    intros j,
    dsimp,
    apply (D.π.app j).level_continuous,
  end }

def limit_cone_is_limit : is_limit (limit_cone G) :=
{ lift := λ S, limit_cone_lift _ _,
  fac' := begin
    intros S j,
    ext,
    change (limit_cone G).π.app j _ = _,
    dsimp [limit_cone_lift, limit_cone, limit_cone_lift_map, proj],
    simpa,
  end,
  uniq' := begin
    intros S m h,
    ext,
    dsimp [limit_cone_lift, limit_cone_lift_map],
    rw ← (m x).preimage_spec,
    apply quotient.sound',
    refine ⟨_, le_sup_left, le_sup_right, _⟩,
    ext j,
    dsimp,
    simp only [cone_point_type_filt.trans_apply, coe_cast_le, coe_cast_le'],
    specialize h j,
    apply_fun (λ e, e x) at h,
    exact h,
  end }

-- This is the goal of this section...
instance : has_limit G := has_limit.mk ⟨limit_cone _, limit_cone_is_limit _⟩

instance : has_limits CompHausFiltPseuNormGrp₁ :=
⟨λ J hJ, { has_limit := λ G, by resetI; apply_instance }⟩

instance (c : ℝ≥0) : preserves_limit G (level.obj c) :=
preserves_limit_of_preserves_limit_cone (limit_cone_is_limit _)
{ lift := λ S,
    (CompHaus.limit_cone_is_limit ((cone_point_diagram G).obj (as_small.up.obj c))).lift
    _ ≫ (cone_point_type.filt_iso _ _).inv,
  fac' := begin
    intros S j,
    dsimp,
    rw category.assoc,
    convert (CompHaus.limit_cone_is_limit
      ((cone_point_diagram G).obj (as_small.up.obj c))).fac S j,
    ext ⟨t,ht⟩,
    dsimp [limit_cone, cone_point_type.filt_iso, cone_point_type.filt_homeo,
      homeomorph.homeomorph_of_continuous_open, cone_point_type.filt_equiv,
      level, proj, CompHaus.limit_cone, Top.limit_cone],
    simpa,
  end,
  uniq' := begin
    intros S m hm,
    rw iso.eq_comp_inv,
    apply (CompHaus.limit_cone_is_limit ((cone_point_diagram G).obj (as_small.up.obj c))).uniq,
    intros j,
    rw [← hm, category.assoc],
    congr' 1,
    rw ← iso.eq_inv_comp,
    ext ⟨t,ht⟩,
    dsimp [limit_cone, cone_point_type.filt_iso, cone_point_type.filt_homeo,
      homeomorph.homeomorph_of_continuous_open, cone_point_type.filt_equiv,
      level, proj, CompHaus.limit_cone, Top.limit_cone],
    simpa,
  end } .

instance (c : ℝ≥0) : preserves_limits (level.obj c) :=
{ preserves_limits_of_shape := λ J _, by exactI
  { preserves_limit := λ G, by apply_instance, } }

lemma mem_filtration_iff_of_is_limit (C : cone G) (hC : is_limit C) (c : ℝ≥0) (x : C.X) :
  x ∈ pseudo_normed_group.filtration C.X c ↔
  (∀ j : J, C.π.app j x ∈ pseudo_normed_group.filtration (G.obj j) c) :=
begin
  split,
  { intros h j,
    apply (C.π.app j).strict h },
  { intro h,
    let E := limit_cone G,
    let e : C ≅ E := hC.unique_up_to_iso (limit_cone_is_limit _),
    let eX : C.X ≅ E.X := (cones.forget _).map_iso e,
    let w := eX.hom x,
    have hw : ∀ j, E.π.app j w ∈ filtration (G.obj j) c,
    { intros j,
      dsimp only [w],
      change (eX.hom ≫ E.π.app _) _ ∈ _,
      dsimp only [eX, functor.map_iso, cones.forget],
      convert h j,
      simp },
    suffices : w ∈ filtration (limit_cone G).X c,
    { convert eX.inv.strict this,
      change _ = (eX.hom ≫ eX.inv) x,
      rw iso.hom_inv_id,
      refl },
    change ∃ z, _,
    refine ⟨⟨λ j, ⟨_, hw _⟩, _⟩, _⟩,
    { intros i j f,
      ext1,
      dsimp,
      change (E.π.app i ≫ G.map f) _ = _,
      rw E.w },
    { obtain ⟨i,z,hz⟩ := cone_point_type.incl_jointly_surjective w,
      let d : ℝ≥0 := i ⊔ c,
      conv_rhs { rw ← hz },
      rw ← cone_point_type.incl_trans (le_sup_left : i ≤ d),
      rw ← cone_point_type.incl_trans (le_sup_right : c ≤ d),
      congr' 1,
      dsimp [cone_point_type_filt.trans],
      ext j,
      dsimp,
      change E.π.app j _ = _,
      rw ← hz,
      dsimp [E, limit_cone, proj],
      simp } }
end

lemma is_limit_ext (C : cone G) (hC : is_limit C) (x y : C.X)
  (h : ∀ j, C.π.app j x = C.π.app j y) : x = y :=
begin
  let E := limit_cone G,
  let e : C ≅ E := hC.unique_up_to_iso (limit_cone_is_limit _),
  let eX : C.X ≅ E.X := (cones.forget _).map_iso e,
  apply_fun eX.hom,
  swap,
  { intros a b hh,
    apply_fun (λ e, eX.inv e) at hh,
    change (eX.hom ≫ eX.inv) _ = (eX.hom ≫ eX.inv) _ at hh,
    simpa only [iso.hom_inv_id] using hh },
  have hh : ∀ j, (E.π.app j) (eX.hom x) = (E.π.app j) (eX.hom y),
  { intros j,
    change (eX.hom ≫ E.π.app j) x = (eX.hom ≫ E.π.app j) y,
    convert h j using 2,
    all_goals { simp } },
  obtain ⟨ca,a,ha⟩ := cone_point_type.incl_jointly_surjective (eX.hom x),
  obtain ⟨cb,b,hb⟩ := cone_point_type.incl_jointly_surjective (eX.hom y),
  rw [← ha, ← hb] at ⊢ hh,
  let d : ℝ≥0 := ca ⊔ cb,
  rw ← cone_point_type.incl_trans (le_sup_left : ca ≤ d) at ⊢ hh,
  rw ← cone_point_type.incl_trans (le_sup_right : cb ≤ d) at ⊢ hh,
  congr' 1,
  ext j,
  specialize hh j,
  convert hh using 1,
  all_goals { dsimp [E, limit_cone, proj],
    simp },
end

end limits

section products

/-!
In this section, we construct explicit finite products.
-/

def product {α : Type u} [fintype α] (X : α → CompHausFiltPseuNormGrp₁.{u}) :
  CompHausFiltPseuNormGrp₁.{u} :=
{ M := Π i, X i,
  exhaustive' := begin
    intro m,
    choose cs hcs using (λ i, (X i).exhaustive (m i)),
    have : ∃ c : ℝ≥0, ∀ i, cs i ≤ c,
    { use finset.univ.sup cs,
      intros i,
      apply finset.le_sup (finset.mem_univ i) },
    obtain ⟨c,hc⟩ := this,
    refine ⟨c, λ i, pseudo_normed_group.filtration_mono (hc i) (hcs i)⟩,
  end }

@[simps]
def product.π {α : Type u} [fintype α] (X : α → CompHausFiltPseuNormGrp₁.{u}) (i : α) :
  product X ⟶ X i :=
{ to_fun := λ m, m i,
  map_zero' := rfl,
  map_add' := λ x y, rfl,
  strict' := λ c x hx, hx i,
  continuous' := begin
    -- This can be golfed.
    intros c,
    have h : inducing (pseudo_normed_group.filtration_pi_equiv (λ i, X i) c) := ⟨rfl⟩,
    let e : ↥(pseudo_normed_group.filtration ↥(product X) c) →
      ↥(pseudo_normed_group.filtration ↥(X i) c) :=
      pseudo_normed_group.level (λ (m : ↥(product X)), m i) _ c,
    swap,
    { intros c x hx,
      apply hx },
    change continuous e,
    have : e = _ ∘ (pseudo_normed_group.filtration_pi_equiv (λ i, X i) c),
    rotate 2,
    { intros x, exact x i },
    { ext, refl },
    erw [this],
    apply continuous.comp,
    apply continuous_apply,
    refine inducing.continuous h
  end }

@[simps]
def product.lift {α : Type u} [fintype α] (X : α → CompHausFiltPseuNormGrp₁.{u})
  (M : CompHausFiltPseuNormGrp₁.{u}) (f : Π i, M ⟶ X i) :
  M ⟶ product X :=
{ to_fun := λ m i, f _ m,
  map_zero' := by { ext, simp },
  map_add' := by { intros, ext, simp },
  strict' := λ c x hx i, (f i).strict hx,
  continuous' := begin
    intros c,
    have h : inducing (pseudo_normed_group.filtration_pi_equiv (λ i, X i) c) := ⟨rfl⟩,
    rw [h.continuous_iff, continuous_pi_iff],
    intros i,
    exact (f i).continuous' c,
  end }

@[simp, reassoc]
lemma product.lift_π {α : Type u} [fintype α] (X : α → CompHausFiltPseuNormGrp₁.{u})
  (M : CompHausFiltPseuNormGrp₁.{u}) (f : Π i, M ⟶ X i) (i) :
  product.lift X M f ≫ product.π X i = f i := by { ext, simp }

lemma product.lift_unique {α : Type u} [fintype α] (X : α → CompHausFiltPseuNormGrp₁.{u})
  (M : CompHausFiltPseuNormGrp₁.{u}) (f : Π i, M ⟶ X i) (g : M ⟶ product X)
  (hg : ∀ i, g ≫ product.π X i = f i) : g = product.lift X M f :=
by { ext, simp [← hg] }

lemma product.hom_ext {α : Type u} [fintype α] (X : α → CompHausFiltPseuNormGrp₁.{u})
  (M : CompHausFiltPseuNormGrp₁.{u}) (g₁ g₂ : M ⟶ product X)
  (h : ∀ i, g₁ ≫ product.π X i = g₂ ≫ product.π X i) : g₁ = g₂ :=
begin
  rw [product.lift_unique X M _ g₁ (λ i, rfl), product.lift_unique X M _ g₂ (λ i, rfl)],
  simp [h],
end

end products

end CompHausFiltPseuNormGrp₁
