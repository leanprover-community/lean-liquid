import category_theory.concrete_category.bundled_hom
import topology.category.Profinite
import data.equiv.fin
--import for_mathlib.concrete
import for_mathlib.CompHaus
import for_mathlib.topology

import pseudo_normed_group.with_Tinv

/-!

# The category of profinitely filtered pseudo-normed groups.

The category of profinite pseudo-normed groups, and the category of
profinitely filtered pseudo-normed groups equipped with an action of T⁻¹.

-/
universe variables u

open category_theory
open_locale nnreal

local attribute [instance] type_pow

noncomputable theory

/-- The category of CompHaus-ly filtered pseudo-normed groups. -/
def CompHausFiltPseuNormGrp : Type (u+1) :=
bundled comphaus_filtered_pseudo_normed_group

namespace CompHausFiltPseuNormGrp

def bundled_hom : bundled_hom @comphaus_filtered_pseudo_normed_group_hom :=
⟨@comphaus_filtered_pseudo_normed_group_hom.to_fun,
 @comphaus_filtered_pseudo_normed_group_hom.id,
 @comphaus_filtered_pseudo_normed_group_hom.comp,
 @comphaus_filtered_pseudo_normed_group_hom.coe_inj⟩

local attribute [instance] bundled_hom
attribute [derive [large_category, concrete_category]] CompHausFiltPseuNormGrp

instance : has_coe_to_sort CompHausFiltPseuNormGrp Type* := bundled.has_coe_to_sort

instance (M : CompHausFiltPseuNormGrp) : comphaus_filtered_pseudo_normed_group M := M.str

/-- Construct a bundled `CompHausFiltPseuNormGrp` from the underlying type and typeclass. -/
def of (M : Type u) [comphaus_filtered_pseudo_normed_group M] : CompHausFiltPseuNormGrp :=
bundled.of M

end CompHausFiltPseuNormGrp

/-- The category of CompHaus-ly filtered pseudo-normed groups with strict morphisms. -/
structure CompHausFiltPseuNormGrp₁ : Type (u+1) :=
(M : Type u)
[str : comphaus_filtered_pseudo_normed_group M]
(exhaustive' : ∀ m : M, ∃ c, m ∈ pseudo_normed_group.filtration M c)


namespace CompHausFiltPseuNormGrp₁

instance : has_coe_to_sort CompHausFiltPseuNormGrp₁ Type* := ⟨λ M, M.M⟩
instance (M : CompHausFiltPseuNormGrp₁) : comphaus_filtered_pseudo_normed_group M := M.str

lemma exhaustive (M : CompHausFiltPseuNormGrp₁) (m : M) :
  ∃ c, m ∈ pseudo_normed_group.filtration M c := M.exhaustive' _

/-
def bundled_hom : bundled_hom @strict_comphaus_filtered_pseudo_normed_group_hom :=
⟨@strict_comphaus_filtered_pseudo_normed_group_hom.to_fun,
 @strict_comphaus_filtered_pseudo_normed_group_hom.id,
 @strict_comphaus_filtered_pseudo_normed_group_hom.comp,
 @strict_comphaus_filtered_pseudo_normed_group_hom.coe_inj⟩

local attribute [instance] bundled_hom
attribute [derive [has_coe_to_sort, large_category, concrete_category]] CompHausFiltPseuNormGrp₁
-/

instance : large_category CompHausFiltPseuNormGrp₁.{u} :=
{ hom := λ A B, strict_comphaus_filtered_pseudo_normed_group_hom A B,
  id := λ A, strict_comphaus_filtered_pseudo_normed_group_hom.id,
  comp := λ A B C f g, g.comp f }

def enlarging_functor : CompHausFiltPseuNormGrp₁ ⥤ CompHausFiltPseuNormGrp :=
{ obj := λ M, CompHausFiltPseuNormGrp.of M,
  map := λ M₁ M₂ f, f.to_chfpsng_hom }

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
  end }

end limits

end CompHausFiltPseuNormGrp₁

/-- The category of profinitely filtered pseudo-normed groups. -/
def ProFiltPseuNormGrp : Type (u+1) :=
bundled profinitely_filtered_pseudo_normed_group

/-- The category of profinitely filtered pseudo-normed groups with action of `T⁻¹`. -/
def ProFiltPseuNormGrpWithTinv (r : ℝ≥0) : Type (u+1) :=
bundled (@profinitely_filtered_pseudo_normed_group_with_Tinv r)

namespace ProFiltPseuNormGrp

local attribute [instance] CompHausFiltPseuNormGrp.bundled_hom

def bundled_hom : bundled_hom.parent_projection
  @profinitely_filtered_pseudo_normed_group.to_comphaus_filtered_pseudo_normed_group := ⟨⟩

local attribute [instance] bundled_hom

attribute [derive [large_category, concrete_category]] ProFiltPseuNormGrp

instance : has_coe_to_sort ProFiltPseuNormGrp Type* := bundled.has_coe_to_sort

instance : has_forget₂ ProFiltPseuNormGrp CompHausFiltPseuNormGrp := bundled_hom.forget₂ _ _

@[simps]
def to_CompHausFilt : ProFiltPseuNormGrp ⥤ CompHausFiltPseuNormGrp := forget₂ _ _

/-- Construct a bundled `ProFiltPseuNormGrp` from the underlying type and typeclass. -/
def of (M : Type u) [profinitely_filtered_pseudo_normed_group M] : ProFiltPseuNormGrp :=
bundled.of M

instance : has_zero ProFiltPseuNormGrp := ⟨of punit⟩

instance : inhabited ProFiltPseuNormGrp := ⟨0⟩

instance (M : ProFiltPseuNormGrp) : profinitely_filtered_pseudo_normed_group M := M.str

@[simp] lemma coe_of (V : Type u) [profinitely_filtered_pseudo_normed_group V] : (ProFiltPseuNormGrp.of V : Type u) = V := rfl

@[simp] lemma coe_id (V : ProFiltPseuNormGrp) : ⇑(𝟙 V) = id := rfl

@[simp] lemma coe_comp {A B C : ProFiltPseuNormGrp} (f : A ⟶ B) (g : B ⟶ C) :
  ⇑(f ≫ g) = g ∘ f := rfl

@[simp] lemma coe_comp_apply {A B C : ProFiltPseuNormGrp} (f : A ⟶ B) (g : B ⟶ C) (x : A) :
  (f ≫ g) x = g (f x) := rfl

open pseudo_normed_group

section

variables (M : Type*) [profinitely_filtered_pseudo_normed_group M] (c : ℝ≥0)

instance : t2_space (Top.of (filtration M c)) := by { dsimp, apply_instance }
instance : totally_disconnected_space (Top.of (filtration M c)) := by { dsimp, apply_instance }
instance : compact_space (Top.of (filtration M c)) := by { dsimp, apply_instance }

end

end ProFiltPseuNormGrp

structure ProFiltPseuNormGrp₁ : Type (u+1) :=
(M : Type u)
[str : profinitely_filtered_pseudo_normed_group M]
(exhaustive' : ∀ m : M, ∃ c, m ∈ pseudo_normed_group.filtration M c)

namespace ProFiltPseuNormGrp₁

instance : has_coe_to_sort ProFiltPseuNormGrp₁ Type* := ⟨λ M, M.M⟩
instance (M : ProFiltPseuNormGrp₁) : profinitely_filtered_pseudo_normed_group M := M.str

lemma exhaustive (M : ProFiltPseuNormGrp₁) (m : M) :
  ∃ c, m ∈ pseudo_normed_group.filtration M c := M.exhaustive' m

instance : large_category ProFiltPseuNormGrp₁.{u} :=
{ hom := λ A B, strict_comphaus_filtered_pseudo_normed_group_hom A B,
  id := λ A, strict_comphaus_filtered_pseudo_normed_group_hom.id,
  comp := λ A B C f g, g.comp f }

def enlarging_functor : ProFiltPseuNormGrp₁ ⥤ ProFiltPseuNormGrp :=
{ obj := λ M, ProFiltPseuNormGrp.of M,
  map := λ M₁ M₂ f, f.to_chfpsng_hom }

instance : concrete_category ProFiltPseuNormGrp₁.{u} :=
{ forget :=
  { obj := λ M, M.M,
    map := λ A B f, f },
  forget_faithful := ⟨⟩ } .

def to_CHFPNG₁ : ProFiltPseuNormGrp₁.{u} ⥤ CompHausFiltPseuNormGrp₁.{u} :=
{ obj := λ M,
  { M := M,
    exhaustive' := M.exhaustive },
  map := λ A B f, f }

def limit_cone {J : Type u} [small_category J] (K : J ⥤ ProFiltPseuNormGrp₁.{u}) :
  limits.cone K :=
{ X :=
  { M := (CompHausFiltPseuNormGrp₁.limit_cone (K ⋙ to_CHFPNG₁)).X,
    str :=
    { continuous_add' := comphaus_filtered_pseudo_normed_group.continuous_add',
      continuous_neg' := comphaus_filtered_pseudo_normed_group.continuous_neg',
      continuous_cast_le := comphaus_filtered_pseudo_normed_group.continuous_cast_le,
      td := begin
        intro c,
        let E := (CompHausFiltPseuNormGrp₁.cone_point_type.filt_homeo (K ⋙ to_CHFPNG₁) c),
        haveI : totally_disconnected_space
          (CompHausFiltPseuNormGrp₁.cone_point_type_filt (K ⋙ to_CHFPNG₁) c) :=
        begin
          dsimp [CompHausFiltPseuNormGrp₁.cone_point_type_filt],
          apply_instance,
        end,
        apply E.symm.totally_disconnected_space,
      end,
      ..(infer_instance : pseudo_normed_group _) },
    exhaustive' :=  CompHausFiltPseuNormGrp₁.exhaustive _ },
  π :=
  { app := λ j, (CompHausFiltPseuNormGrp₁.limit_cone (K ⋙ to_CHFPNG₁)).π.app j,
    naturality' := (CompHausFiltPseuNormGrp₁.limit_cone (K ⋙ to_CHFPNG₁)).π.naturality } }

instance {J : Type u} [small_category J] : creates_limits_of_shape J to_CHFPNG₁ :=
{ creates_limit := λ K,
  { reflects := λ C hC,
    { lift := λ S, hC.lift (to_CHFPNG₁.map_cone S),
      fac' := λ S j, hC.fac _ _,
      uniq' := λ S m h, hC.uniq (to_CHFPNG₁.map_cone S) m h },
    lifts := λ C hC,
    { lifted_cone := limit_cone _,
      valid_lift :=
        (CompHausFiltPseuNormGrp₁.limit_cone_is_limit (K ⋙ to_CHFPNG₁)).unique_up_to_iso hC } } }

instance : creates_limits to_CHFPNG₁ := ⟨⟩

def limit_cone_is_limit {J : Type u} [small_category J] (K : J ⥤ ProFiltPseuNormGrp₁.{u}) :
  limits.is_limit (limit_cone K) :=
limits.is_limit_of_reflects to_CHFPNG₁ (CompHausFiltPseuNormGrp₁.limit_cone_is_limit _)

instance : limits.has_limits ProFiltPseuNormGrp₁.{u} :=
has_limits_of_has_limits_creates_limits to_CHFPNG₁

lemma eq_of_π_eq {J : Type u} [small_category J] {K : J ⥤ ProFiltPseuNormGrp₁.{u}}
  (C : limits.cone K) (hC : limits.is_limit C) (x y : C.X)
  (cond : ∀ j, C.π.app j x = C.π.app j y) : x = y :=
begin
  let D := limit_cone K,
  let hD : limits.is_limit D := limit_cone_is_limit _,
  let E : C.X ≅ D.X := hC.cone_point_unique_up_to_iso hD,
  apply_fun E.hom,
  swap, {
    intros a b h,
    apply_fun E.inv at h,
    change (E.hom ≫ E.inv) _ = (E.hom ≫ E.inv) _ at h,
    simpa using h },
  apply quotient.sound',
  refine ⟨_, le_sup_left, le_sup_right, _⟩,
  simp,
  ext j : 3,
  dsimp, simp,
  exact cond j,
end

lemma coe_comp_apply {A B C : ProFiltPseuNormGrp₁} (f : A ⟶ B) (g : B ⟶ C) (x : A) :
  (f ≫ g) x = g (f x) := rfl

end ProFiltPseuNormGrp₁

namespace ProFiltPseuNormGrpWithTinv

variables (r' : ℝ≥0)

instance bundled_hom : bundled_hom (@profinitely_filtered_pseudo_normed_group_with_Tinv_hom r') :=
⟨@profinitely_filtered_pseudo_normed_group_with_Tinv_hom.to_fun r',
 @profinitely_filtered_pseudo_normed_group_with_Tinv_hom.id r',
 @profinitely_filtered_pseudo_normed_group_with_Tinv_hom.comp r',
 @profinitely_filtered_pseudo_normed_group_with_Tinv_hom.coe_inj r'⟩

attribute [derive [λ α, has_coe_to_sort α (Sort*), large_category, concrete_category]]
  ProFiltPseuNormGrpWithTinv

/-- Construct a bundled `ProFiltPseuNormGrpWithTinv` from the underlying type and typeclass. -/
def of (r' : ℝ≥0) (M : Type u) [profinitely_filtered_pseudo_normed_group_with_Tinv r' M] :
  ProFiltPseuNormGrpWithTinv r' :=
bundled.of M

instance : has_zero (ProFiltPseuNormGrpWithTinv r') :=
⟨{ α := punit, str := punit.profinitely_filtered_pseudo_normed_group_with_Tinv r' }⟩

instance : inhabited (ProFiltPseuNormGrpWithTinv r') := ⟨0⟩

instance (M : ProFiltPseuNormGrpWithTinv r') :
  profinitely_filtered_pseudo_normed_group_with_Tinv r' M := M.str

@[simp] lemma coe_of (V : Type u) [profinitely_filtered_pseudo_normed_group_with_Tinv r' V] :
  (ProFiltPseuNormGrpWithTinv.of r' V : Type u) = V := rfl

@[simp] lemma of_coe (M : ProFiltPseuNormGrpWithTinv r') : of r' M = M :=
by { cases M, refl }

@[simp] lemma coe_id (V : ProFiltPseuNormGrpWithTinv r') : ⇑(𝟙 V) = id := rfl

@[simp] lemma coe_comp {A B C : ProFiltPseuNormGrpWithTinv r'} (f : A ⟶ B) (g : B ⟶ C) :
  ⇑(f ≫ g) = g ∘ f := rfl

@[simp] lemma coe_comp_apply {A B C : ProFiltPseuNormGrpWithTinv r'} (f : A ⟶ B) (g : B ⟶ C) (x : A) :
  (f ≫ g) x = g (f x) := rfl
open pseudo_normed_group

section

variables (M : Type*) [profinitely_filtered_pseudo_normed_group_with_Tinv r' M] (c : ℝ≥0)
include r'

instance : t2_space (Top.of (filtration M c)) := by { dsimp, apply_instance }
instance : totally_disconnected_space (Top.of (filtration M c)) := by { dsimp, apply_instance }
instance : compact_space (Top.of (filtration M c)) := by { dsimp, apply_instance }

end

-- @[simps] def Filtration (c : ℝ≥0) : ProFiltPseuNormGrp ⥤ Profinite :=
-- { obj := λ M, ⟨Top.of (filtration M c)⟩,
--   map := λ M₁ M₂ f, ⟨f.level c, f.level_continuous c⟩,
--   map_id' := by { intros, ext, refl },
--   map_comp' := by { intros, ext, refl } }


open pseudo_normed_group profinitely_filtered_pseudo_normed_group_with_Tinv_hom

open profinitely_filtered_pseudo_normed_group_with_Tinv (Tinv)

variables {r'}
variables {M M₁ M₂ : ProFiltPseuNormGrpWithTinv.{u} r'}
variables {f : M₁ ⟶ M₂}

/-- The isomorphism induced by a bijective `profinitely_filtered_pseudo_normed_group_with_Tinv_hom`
whose inverse is strict. -/
def iso_of_equiv_of_strict (e : M₁ ≃+ M₂) (he : ∀ x, f x = e x)
  (strict : ∀ ⦃c x⦄, x ∈ filtration M₂ c → e.symm x ∈ filtration M₁ c) :
  M₁ ≅ M₂ :=
{ hom := f,
  inv := inv_of_equiv_of_strict e he strict,
  hom_inv_id' := by { ext x, simp [inv_of_equiv_of_strict, he] },
  inv_hom_id' := by { ext x, simp [inv_of_equiv_of_strict, he] } }

@[simp]
lemma iso_of_equiv_of_strict.apply (e : M₁ ≃+ M₂) (he : ∀ x, f x = e x)
  (strict : ∀ ⦃c x⦄, x ∈ filtration M₂ c → e.symm x ∈ filtration M₁ c) (x : M₁) :
  (iso_of_equiv_of_strict e he strict).hom x = f x := rfl

@[simp]
lemma iso_of_equiv_of_strict_symm.apply (e : M₁ ≃+ M₂) (he : ∀ x, f x = e x)
  (strict : ∀ ⦃c x⦄, x ∈ filtration M₂ c → e.symm x ∈ filtration M₁ c) (x : M₂) :
  (iso_of_equiv_of_strict e he strict).symm.hom x = e.symm x := rfl

def iso_of_equiv_of_strict'
  (e : M₁ ≃+ M₂)
  (strict' : ∀ c x, x ∈ filtration M₁ c ↔ e x ∈ filtration M₂ c)
  (continuous' : ∀ c, continuous (pseudo_normed_group.level e (λ c x, (strict' c x).1) c))
  (map_Tinv' : ∀ x, e (Tinv x) = Tinv (e x)) :
  M₁ ≅ M₂ :=
@iso_of_equiv_of_strict r' M₁ M₂
 {to_fun := e,
  strict' := λ c x, (strict' c x).1,
  continuous' := continuous',
  map_Tinv' := map_Tinv',
  ..e.to_add_monoid_hom } e (λ _, rfl)
  (by { intros c x hx, rwa [strict', e.apply_symm_apply] })

@[simp]
lemma iso_of_equiv_of_strict'_hom_apply
  (e : M₁ ≃+ M₂)
  (strict' : ∀ c x, x ∈ filtration M₁ c ↔ e x ∈ filtration M₂ c)
  (continuous' : ∀ c, continuous (pseudo_normed_group.level e (λ c x, (strict' c x).1) c))
  (map_Tinv' : ∀ x, e (Tinv x) = Tinv (e x))
  (x : M₁) :
  (iso_of_equiv_of_strict' e strict' continuous' map_Tinv').hom x = e x := rfl

@[simp]
lemma iso_of_equiv_of_strict'_inv_apply
  (e : M₁ ≃+ M₂)
  (strict' : ∀ c x, x ∈ filtration M₁ c ↔ e x ∈ filtration M₂ c)
  (continuous' : ∀ c, continuous (pseudo_normed_group.level e (λ c x, (strict' c x).1) c))
  (map_Tinv' : ∀ x, e (Tinv x) = Tinv (e x))
  (x : M₂) :
  (iso_of_equiv_of_strict' e strict' continuous' map_Tinv').inv x = e.symm x := rfl

variables (r')

@[simps]
def Pow (n : ℕ) : ProFiltPseuNormGrpWithTinv.{u} r' ⥤ ProFiltPseuNormGrpWithTinv.{u} r' :=
{ obj := λ M, of r' $ M ^ n,
  map := λ M₁ M₂ f, profinitely_filtered_pseudo_normed_group_with_Tinv.pi_map r' _ _ (λ i, f),
  map_id' := λ M, by { ext, refl },
  map_comp' := by { intros, ext, refl } }

@[simps]
def Pow_Pow_X_equiv (N n : ℕ) :
  M ^ (N * n) ≃+ (M ^ N) ^ n :=
{ to_fun := ((equiv.curry _ _ _).symm.trans (((equiv.prod_comm _ _).trans fin_prod_fin_equiv).arrow_congr (equiv.refl _))).symm,
  map_add' := λ x y, by { ext, refl },
  .. ((equiv.curry _ _ _).symm.trans (((equiv.prod_comm _ _).trans fin_prod_fin_equiv).arrow_congr (equiv.refl _))).symm }

open profinitely_filtered_pseudo_normed_group
open comphaus_filtered_pseudo_normed_group

@[simps]
def Pow_Pow_X (N n : ℕ) (M : ProFiltPseuNormGrpWithTinv.{u} r') :
  (Pow r' N ⋙ Pow r' n).obj M ≅ (Pow r' (N * n)).obj M :=
iso.symm $
iso_of_equiv_of_strict'
  (Pow_Pow_X_equiv r' N n)
  begin
    intros c x,
    dsimp,
    split; intro h,
    { intros i j, exact h (fin_prod_fin_equiv (j, i)) },
    { intro ij,
      have := h (fin_prod_fin_equiv.symm ij).2 (fin_prod_fin_equiv.symm ij).1,
      dsimp [-fin_prod_fin_equiv_symm_apply] at this,
      simpa only [prod.mk.eta, equiv.apply_symm_apply] using this, },
  end
  begin
    intro c, dsimp,
    rw [← (filtration_pi_homeo (λ _, M ^ N) c).comp_continuous_iff,
        ← (filtration_pi_homeo (λ _, M) c).symm.comp_continuous_iff'],
    apply continuous_pi,
    intro i,
    rw [← (filtration_pi_homeo (λ _, M) c).comp_continuous_iff],
    apply continuous_pi,
    intro j,
    have := @continuous_apply _ (λ _, filtration M c) _ (fin_prod_fin_equiv (j, i)),
    dsimp [function.comp] at this ⊢,
    simpa only [subtype.coe_eta],
  end
  (by { intros, ext, refl })

@[simps hom inv]
def Pow_mul (N n : ℕ) : Pow r' (N * n) ≅ Pow r' N ⋙ Pow r' n :=
nat_iso.of_components (λ M, (Pow_Pow_X r' N n M).symm)
begin
  intros X Y f,
  ext x i j,
  refl,
end

end ProFiltPseuNormGrpWithTinv

structure ProFiltPseuNormGrpWithTinv₁ (r : ℝ≥0) : Type (u+1) :=
(M : Type u)
[str : profinitely_filtered_pseudo_normed_group_with_Tinv r M]
(exhaustive' : ∀ m : M, ∃ c : ℝ≥0, m ∈ pseudo_normed_group.filtration M c)

namespace ProFiltPseuNormGrpWithTinv₁

variable (r : ℝ≥0)

instance : has_coe_to_sort (ProFiltPseuNormGrpWithTinv₁ r) Type* := ⟨λ M, M.M⟩
instance (M : ProFiltPseuNormGrpWithTinv₁ r) :
  profinitely_filtered_pseudo_normed_group_with_Tinv r M := M.str

lemma exhaustive (M : ProFiltPseuNormGrpWithTinv₁ r) (m : M) : ∃ c : ℝ≥0,
  m ∈ pseudo_normed_group.filtration M c := M.exhaustive' m

instance : large_category (ProFiltPseuNormGrpWithTinv₁.{u} r) :=
{ hom := λ A B, profinitely_filtered_pseudo_normed_group_with_Tinv_hom r A B,
  id := λ A, profinitely_filtered_pseudo_normed_group_with_Tinv_hom.id,
  comp := λ A B C f g, g.comp f } .

def enlarging_functor : (ProFiltPseuNormGrpWithTinv₁.{u} r) ⥤ (ProFiltPseuNormGrpWithTinv.{u} r) :=
{ obj := λ M, ProFiltPseuNormGrpWithTinv.of r M,
  map := λ A B f, f }

instance : concrete_category (ProFiltPseuNormGrpWithTinv₁.{u} r) :=
{ forget :=
  { obj := λ M, M,
    map := λ X Y f, f },
  forget_faithful := ⟨⟩ } .

def to_PFPNG₁ : (ProFiltPseuNormGrpWithTinv₁.{u} r) ⥤ ProFiltPseuNormGrp₁.{u} :=
{ obj := λ M,
  { M := M,
    exhaustive' := M.exhaustive' },
  map := λ A B f,
  { to_fun := f,
    map_zero' := f.map_zero,
    map_add' := f.map_add,
    strict' := f.strict,
    continuous' := f.continuous' } }

lemma coe_comp_apply {A B C : ProFiltPseuNormGrpWithTinv₁ r} (f : A ⟶ B) (g : B ⟶ C) (a : A) :
  (f ≫ g) a = g (f a) := rfl

open profinitely_filtered_pseudo_normed_group_with_Tinv

def Tinv_limit_fun_aux {J : Type u} [small_category J] (K : J ⥤ ProFiltPseuNormGrpWithTinv₁ r)
  (x : Σ (c : ℝ≥0), CompHausFiltPseuNormGrp₁.cone_point_type_filt
    ((K ⋙ to_PFPNG₁ r) ⋙ ProFiltPseuNormGrp₁.to_CHFPNG₁) c) (j : J) :
  (pseudo_normed_group.filtration (K.obj j) x.fst) :=
x.2 j

def Tinv_limit_fun'
  {J : Type u} [small_category J] (K : J ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r)
  (c : ℝ≥0) (x : CompHausFiltPseuNormGrp₁.cone_point_type_filt
    ((K ⋙ to_PFPNG₁ r) ⋙ ProFiltPseuNormGrp₁.to_CHFPNG₁) c) :
  (Σ c, CompHausFiltPseuNormGrp₁.cone_point_type_filt
    ((K ⋙ to_PFPNG₁ r) ⋙ ProFiltPseuNormGrp₁.to_CHFPNG₁) c) :=
⟨r⁻¹ * c, λ j,
  ⟨Tinv (Tinv_limit_fun_aux r K ⟨c,x⟩ j : K.obj j),
    (Tinv_mem_filtration _ _ (Tinv_limit_fun_aux r K ⟨c,x⟩ j).2)⟩,
  begin
    intros i j f,
    ext1,
    show (K.map f) (Tinv _) = Tinv _,
    rw (K.map f).map_Tinv, congr' 1,
    simpa only [functor.comp_map, subtype.val_eq_coe, subtype.ext_iff] using x.2 f,
  end⟩

def Tinv_limit_fun
  {J : Type u} [small_category J] (K : J ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r) :
  ((ProFiltPseuNormGrp₁.limit_cone (K ⋙ to_PFPNG₁ r)).X) →
    ((ProFiltPseuNormGrp₁.limit_cone (K ⋙ to_PFPNG₁ r)).X) :=
quotient.map' (λ x, Tinv_limit_fun' r K x.1 x.2)
begin
  rintros x y ⟨c, h₁, h₂, h⟩,
  refine ⟨r⁻¹ * c, mul_le_mul' le_rfl h₁, mul_le_mul' le_rfl h₂, _⟩,
  ext j,
  show Tinv (Tinv_limit_fun_aux r K x j : K.obj j) = Tinv (Tinv_limit_fun_aux r K y j : K.obj j),
  congr' 1,
  rw [subtype.ext_iff, function.funext_iff] at h,
  specialize h j, rwa [subtype.ext_iff] at h,
end

open CompHausFiltPseuNormGrp₁ CompHausFiltPseuNormGrp₁.cone_point_type

lemma Tinv_limit_fun_incl
  {J : Type u} [small_category J] (K : J ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r) (c : ℝ≥0) (x) :
  Tinv_limit_fun r K (incl c x) = incl (r⁻¹ * c) (Tinv_limit_fun' r K c x).2 := rfl

@[simps]
def Tinv_limit_add_monoid_hom
  {J : Type u} [small_category J] (K : J ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r) :
  ((ProFiltPseuNormGrp₁.limit_cone (K ⋙ to_PFPNG₁ r)).X) →+
    ((ProFiltPseuNormGrp₁.limit_cone (K ⋙ to_PFPNG₁ r)).X) :=
{ to_fun := Tinv_limit_fun r K,
  map_zero' :=
  begin
    apply quotient.sound',
    dsimp only,
    refine ⟨0, _, le_rfl, _⟩; dsimp only [Tinv_limit_fun'],
    { rw [mul_zero] },
    { ext j, exact Tinv.map_zero }
  end,
  map_add' :=
  begin
    rintros ⟨cx, x⟩ ⟨cy, y⟩,
    show Tinv_limit_fun r K (incl cx x + incl cy y) =
      Tinv_limit_fun r K (incl cx x) + Tinv_limit_fun r K (incl cy y),
    simp only [incl_add_incl, Tinv_limit_fun_incl],
    apply quotient.sound',
    dsimp only,
    refine ⟨_, le_rfl, _, _⟩; simp only [mul_add],
    ext j, refine Tinv.map_add _ _,
  end }

open pseudo_normed_group ProFiltPseuNormGrp₁ CompHausFiltPseuNormGrp₁

lemma Tinv_limit_aux {J : Type u} [small_category J] (K : J ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r)
  (c : ℝ≥0) (x : ((ProFiltPseuNormGrp₁.limit_cone (K ⋙ to_PFPNG₁ r)).X))
  (hx : x ∈ filtration (ProFiltPseuNormGrp₁.limit_cone (K ⋙ to_PFPNG₁ r)).X c) :
  Tinv_limit_add_monoid_hom r K x ∈
    filtration (ProFiltPseuNormGrp₁.limit_cone (K ⋙ to_PFPNG₁ r)).X (r⁻¹ * c) :=
begin
  obtain ⟨x,rfl⟩ := hx,
  dsimp only [Tinv_limit_add_monoid_hom_apply, Tinv_limit_fun_incl],
  exact ⟨_,rfl⟩,
end

-- TODO: break up this proof into pieces.
def Tinv_limit {J : Type u} [small_category J] (K : J ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r) :
  comphaus_filtered_pseudo_normed_group_hom
    ((ProFiltPseuNormGrp₁.limit_cone (K ⋙ to_PFPNG₁ r)).X)
    ((ProFiltPseuNormGrp₁.limit_cone (K ⋙ to_PFPNG₁ r)).X) :=
comphaus_filtered_pseudo_normed_group_hom.mk_of_bound (Tinv_limit_add_monoid_hom r K) r⁻¹
begin
  intro c,
  fsplit,
  { apply Tinv_limit_aux },
  { let X := ((ProFiltPseuNormGrp₁.limit_cone (K ⋙ to_PFPNG₁ r)).X),
    let F : filtration X c → filtration X (r⁻¹ * c) := λ x,
      ⟨Tinv_limit_add_monoid_hom r K x, Tinv_limit_aux _ _ _ _ x.2⟩,
    change continuous F,
    let e := filt_homeo (K ⋙ to_PFPNG₁ _ ⋙ to_CHFPNG₁),
    suffices : continuous (e (r⁻¹ * c) ∘ F ∘ (e c).symm), by simpa,
    let I : Π (j : J), comphaus_filtered_pseudo_normed_group_hom (K.obj j) (K.obj j) :=
      λ j, Tinv,
    let G : cone_point_type_filt (K ⋙ to_PFPNG₁ _ ⋙ to_CHFPNG₁) c →
      cone_point_type_filt (K ⋙ to_PFPNG₁ _ ⋙ to_CHFPNG₁) (r⁻¹ * c) :=
      λ x, ⟨λ j, ⟨I j (x j).1, _⟩, _⟩,
    rotate,
    { apply Tinv_bound_by, exact (x j).2 },
    { intros i j e,
      have := x.2 e,
      ext,
      dsimp,
      apply_fun (λ e, e.val) at this,
      change _ = I j (x.val j).val,
      rw ← this,
      apply (K.map e).map_Tinv },
    have : continuous G,
    { apply continuous_subtype_mk,
      apply continuous_pi,
      intros i,
      let G1 : cone_point_type_filt (K ⋙ to_PFPNG₁ _ ⋙ to_CHFPNG₁) c →
        filtration (K.obj i) c := λ x, x i,
      let G2 : filtration (K.obj i) c → filtration (K.obj i) (r⁻¹ * c) :=
        λ x, ⟨I i x, _⟩,
      swap, { apply Tinv_bound_by, exact x.2 },
      change continuous (G2 ∘ G1),
      apply continuous.comp,
      { apply comphaus_filtered_pseudo_normed_group_hom.continuous, intros x, refl },
      { let G11 : cone_point_type_filt (K ⋙ to_PFPNG₁ _ ⋙ to_CHFPNG₁) c →
          Π j : J, filtration (K.obj j) c := λ x, x,
        let G12 : (Π j : J, filtration (K.obj j) c) → filtration (K.obj i) c := λ x, x i,
        change continuous (G12 ∘ G11),
        apply continuous.comp,
        apply continuous_apply,
        apply continuous_subtype_coe } },
    convert this,
    ext : 1,
    dsimp,
    apply_fun (e (r⁻¹ * c)).symm,
    simp,
    ext, refl },
end

instance {J : Type u} [small_category J] (K : J ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r) :
  profinitely_filtered_pseudo_normed_group_with_Tinv r
    (ProFiltPseuNormGrp₁.limit_cone (K ⋙ to_PFPNG₁ r)).X :=
{ Tinv := Tinv_limit r K,
  Tinv_mem_filtration := comphaus_filtered_pseudo_normed_group_hom.mk_of_bound_bound_by _ _ _,
  ..(infer_instance : profinitely_filtered_pseudo_normed_group _) }

def limit_cone {J : Type u} [small_category J] (K : J ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r) :
  limits.cone K :=
{ X :=
  { M := (ProFiltPseuNormGrp₁.limit_cone (K ⋙ to_PFPNG₁ r)).X,
    exhaustive' := (ProFiltPseuNormGrp₁.limit_cone (K ⋙ to_PFPNG₁ r)).X.exhaustive },
  π :=
  { app := λ j,
    { map_Tinv' := begin
        rintro ⟨⟨c,x⟩⟩,
        dsimp [Tinv, Tinv_limit, Tinv_limit_fun, Tinv_limit_fun', Tinv_limit_fun_aux],
        dsimp [ProFiltPseuNormGrp₁.limit_cone, CompHausFiltPseuNormGrp₁.limit_cone],
        erw quotient.map'_mk',
        change proj (K ⋙ to_PFPNG₁ r ⋙ to_CHFPNG₁) j (incl _ _) = _,
        change _ = Tinv (proj _ _ (incl _ _)),
        dsimp [proj],
        simpa,
      end,
      ..(ProFiltPseuNormGrp₁.limit_cone (K ⋙ to_PFPNG₁ r)).π.app j },
  naturality' := begin
    intros i j e,
    ext1 x,
    have := (ProFiltPseuNormGrp₁.limit_cone (K ⋙ to_PFPNG₁ r)).π.naturality e,
    apply_fun (λ e, e x) at this,
    exact this,
  end } } .

instance {J : Type u} [small_category J] : creates_limits_of_shape J (to_PFPNG₁ r) :=
{ creates_limit := λ K,
  { reflects := λ C hC,
    { lift := λ S,
      { map_Tinv' := begin
          intros x,
          apply ProFiltPseuNormGrp₁.eq_of_π_eq _ hC,
          intros j,
          erw [← ProFiltPseuNormGrp₁.coe_comp_apply, ← ProFiltPseuNormGrp₁.coe_comp_apply,
            hC.fac],
          dsimp,
          change S.π.app _ _ = C.π.app _ _,
          rw [(S.π.app _).map_Tinv, (C.π.app _).map_Tinv],
          congr' 1,
          change _ = ((to_PFPNG₁ r).map (C.π.app j)) _,
          erw [← ProFiltPseuNormGrp₁.coe_comp_apply, hC.fac],
          refl,
        end,
        ..hC.lift ((to_PFPNG₁ r).map_cone S) },
      fac' := begin
        intros S j,
        ext1 x,
        have := hC.fac ((to_PFPNG₁ r).map_cone S) j,
        apply_fun (λ e, e x) at this,
        exact this,
      end,
      uniq' := begin
        intros S m h,
        ext1 x,
        have := hC.uniq ((to_PFPNG₁ r).map_cone S) ((to_PFPNG₁ r).map m) _,
        apply_fun (λ e, e x) at this,
        exact this,
        { intros j,
          ext y,
          specialize h j,
          apply_fun (λ e, e y) at h,
          exact h },
      end },
    lifts := λ C hC,
    { lifted_cone := limit_cone r K,
      valid_lift :=
        (ProFiltPseuNormGrp₁.limit_cone_is_limit (K ⋙ to_PFPNG₁ r)).unique_up_to_iso hC } } }

instance : creates_limits (to_PFPNG₁ r) := ⟨⟩

def limit_cone_is_limit {J : Type u} [small_category J]
  (K : J ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r) : limits.is_limit (limit_cone r K) :=
limits.is_limit_of_reflects (to_PFPNG₁ r) (ProFiltPseuNormGrp₁.limit_cone_is_limit _)

instance : limits.has_limits (ProFiltPseuNormGrpWithTinv₁.{u} r) :=
has_limits_of_has_limits_creates_limits (to_PFPNG₁ r)

end ProFiltPseuNormGrpWithTinv₁
