import category_theory.concrete_category.bundled_hom
import topology.category.Profinite
import data.equiv.fin
import for_mathlib.concrete
import for_mathlib.CompHaus

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
attribute [derive [has_coe_to_sort, large_category, concrete_category]] CompHausFiltPseuNormGrp

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

instance : has_coe_to_sort CompHausFiltPseuNormGrp₁ := ⟨Type*, λ M, M.M⟩
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

open category_theory.limits

/-- This is a bifunctor which associates to each `c : ℝ≥0` and `j : J`,
  the `c`-th term of the filtration of `G.obj j`. -/
def cone_point_diagram : as_small.{u} ℝ≥0 ⥤ J ⥤ CompHaus.{u} :=
as_small.down ⋙ level ⋙ (whiskering_left _ _ _).obj G

def cone_point_type : Type u :=
colimit (cone_point_diagram G ⋙ lim ⋙ forget _)

def cone_point_type_filt (c : ℝ≥0) : CompHaus :=
limit ((cone_point_diagram G).obj (as_small.up.obj c))

def incl (c : ℝ≥0) : cone_point_type_filt G c → cone_point_type G :=
colimit.ι (cone_point_diagram G ⋙ lim ⋙ forget _) (as_small.up.obj c)

def trans {c₁ c₂ : ℝ≥0} (h : c₁ ≤ c₂) :
  cone_point_type_filt G c₁ ⟶ cone_point_type_filt G c₂ :=
(cone_point_diagram G ⋙ lim).map (as_small.up.map $ hom_of_le h)

def proj (c : ℝ≥0) (j : J) : cone_point_type_filt G c ⟶ (level.obj c).obj (G.obj j) :=
limit.π _ _

lemma proj_trans {c₁ c₂ : ℝ≥0} (h : c₁ ≤ c₂) (j : J) :
  trans G h ≫ proj G c₂ j = proj G _ j ≫ (level.map $ hom_of_le h).app _ :=
begin
  dsimp [trans, proj, cone_point_diagram],
  simp,
end


@[simp] lemma map_proj {c : ℝ≥0} {i j : J} (e : i ⟶ j) :
  proj G c i ≫ (level.obj c).map (G.map e) = proj G c j :=
limit.w _ _

lemma proj_ext {c : ℝ≥0} (a b : cone_point_type_filt G c) (h : ∀ i, proj G c i a = proj G c i b) :
  a = b := concrete_category.limit.term_ext _ h

lemma cone_point_diagram_map_injective {c₁ c₂ : as_small.{u} ℝ≥0} (e : c₁ ⟶ c₂) :
  function.injective ((cone_point_diagram G ⋙ lim ⋙ forget CompHaus).map e) :=
begin
  intros x y h,
  apply concrete_category.limit.term_ext,
  intros j,
  apply_fun (concrete_category.limit.equiv _).symm at h,
  apply_fun (λ e, (e.val j).val) at h,
  ext1,
  convert h using 1,
  all_goals { dsimp [concrete_category.limit.equiv, types.limit_cone_is_limit,
      is_limit.cone_point_unique_up_to_iso, lim_map, is_limit.map],
    simp_rw ← CompHaus.coe_comp_apply,
    erw limit.lift_π,
    refl },
end

lemma trans_injective {c₁ c₂ : ℝ≥0} (h : c₁ ≤ c₂) : function.injective (trans G h) :=
cone_point_diagram_map_injective _ _

-- This should be generalized to filtered colimits in a concrete category
-- where the forgetful functor preserves colimits.
lemma incl_injective (c : ℝ≥0) : function.injective (incl G c) :=
begin
  intros a b h,
  erw limits.types.filtered_colimit.colimit_eq_iff at h,
  obtain ⟨k,e₁,e₂,h⟩ := h,
  have : e₁ = e₂, by ext,
  rw this at h,
  apply cone_point_diagram_map_injective _ e₂,
  exact h,
end

lemma incl_trans {c₁ c₂ : ℝ≥0} (h : c₁ ≤ c₂) :
  incl G c₂ ∘ trans G h = incl G c₁ :=
begin
  ext1 x,
  have := colimit.w (cone_point_diagram G ⋙ lim ⋙ forget _) (as_small.up.map (hom_of_le h)),
  apply_fun (λ e, e x) at this,
  exact this,
end

lemma incl_trans_apply {c₁ c₂ : ℝ≥0} (h : c₁ ≤ c₂) (x : cone_point_type_filt G c₁) :
  incl G c₂ (trans G h x) = incl G c₁ x :=
by { change (incl G c₂ ∘ trans G h) x = _, simp [incl_trans] }

lemma incl_eq_incl {c₁ c₂ c : ℝ≥0} (a : cone_point_type_filt G c₁)
  (b : cone_point_type_filt G c₂) (h₁ : c₁ ≤ c) (h₂ : c₂ ≤ c)
  (h : trans G h₁ a = trans G h₂ b) :
  incl G _ a = incl G _ b :=
begin
  rw [← incl_trans _ h₁, ← incl_trans _ h₂],
  dsimp,
  rw h,
end

-- This should be generalized to colimits in a concrete category
-- where the forgetful functor preserves colimits.
lemma incl_jointly_surjective (x : cone_point_type G) :
  ∃ (c : ℝ≥0) (y : cone_point_type_filt G c), x = incl G c y :=
begin
  obtain ⟨⟨c⟩,y,hy⟩ := limits.concrete.is_colimit_exists_rep
    (cone_point_diagram G ⋙ lim ⋙ forget _) (colimit.is_colimit _) x,
  use [c,y],
  exact hy.symm
end

def choose_index (x : cone_point_type G) : ℝ≥0 :=
(incl_jointly_surjective G x).some

def choose_preimage (x : cone_point_type G) :
  (cone_point_type_filt G (choose_index G x)) :=
(incl_jointly_surjective G x).some_spec.some

lemma choose_preimage_spec (x : cone_point_type G) :
  x = incl _ _ (choose_preimage G x) :=
(incl_jointly_surjective G x).some_spec.some_spec

instance (c : ℝ≥0) : has_zero (cone_point_type_filt G c) :=
has_zero.mk (concrete_category.limit.mk _
  (λ j, (0 : pseudo_normed_group.filtration _ _)) begin
    intros i j e,
    dsimp [cone_point_diagram, level],
    ext1,
    simp [(G.map e).map_zero],
  end)

lemma aux (c : ℝ≥0) (j : J) (x : cone_point_type_filt G c) :
  ((proj G _ j (choose_preimage G (incl G _ x))).val : G.obj j) = (proj G _ j x).val :=
begin
  let e := c ⊔ (choose_index G (incl G _ x)),
  have := proj_trans G (le_sup_left : _ ≤ e) j,
  have : (proj G _ j x).val =
    ((proj G c j ≫ (level.map (hom_of_le le_sup_left)).app (G.obj j)) x).val, refl,
  rw this,
  rw ← proj_trans G (le_sup_left : _ ≤ e),
  have : ((proj G (choose_index G (incl G c x)) j) (choose_preimage G (incl G c x))).val =
    ((proj G (choose_index G (incl G c x)) j ≫
    (level.map (hom_of_le le_sup_right)).app (G.obj j)) _).val, refl,
  rw this,
  rw ← proj_trans G (le_sup_right : _ ≤ e),
  dsimp,
  congr' 2,
  apply incl_injective,
  simp_rw incl_trans_apply,
  rw ← choose_preimage_spec G (incl G _ x),
end

instance : has_zero (cone_point_type G) := ⟨incl G 0 0⟩

instance (c : ℝ≥0) : has_neg (cone_point_type_filt G c) := has_neg.mk $
λ x, concrete_category.limit.mk _
  (λ j, (- (proj _ _ _ x) : pseudo_normed_group.filtration _ _))
begin
  intros i j e,
  dsimp [cone_point_diagram, level],
  ext1,
  dsimp,
  rw [(G.map e).map_neg],
  congr' 1,
  change ((proj G c i ≫ (level.obj c).map (G.map e)) x).val = _,
  simp,
end

/-
def neg_nat_trans' : (cone_point_diagram G ⋙ lim ⋙ forget _) ⟶
  (cone_point_diagram G ⋙ lim ⋙ forget _) :=
{ app := λ ⟨c⟩ (x : cone_point_type_filt G c), (-x : cone_point_type_filt G c),
  naturality' := begin
    sorry
  end }
-/

instance : has_neg (cone_point_type G) := has_neg.mk $
λ x, incl G (choose_index G x) (-(choose_preimage G x))

def cone_point_type_filt_add {c₁ c₂ : ℝ≥0} (x : cone_point_type_filt G c₁)
  (y : cone_point_type_filt G c₂) : cone_point_type_filt G (c₁ + c₂) :=
concrete_category.limit.mk _
(λ j, pseudo_normed_group.add' ⟨proj G c₁ j x, proj G c₂ j y⟩)
begin
  intros i j e,
  dsimp [cone_point_diagram, level],
  ext : 1,
  dsimp,
  rw (G.map e).map_add,
  congr' 1,
  { change ((proj G c₁ i ≫ (level.obj c₁).map (G.map e)) x).val = _,
    simp },
  { change ((proj G c₂ i ≫ (level.obj c₂).map (G.map e)) y).val = _,
    simp },
end

instance : has_add (cone_point_type G) := has_add.mk $
λ x y, incl G _ (cone_point_type_filt_add _ (choose_preimage G x) (choose_preimage G y))

lemma zero_add (a : cone_point_type G) : 0 + a = a :=
begin
  change incl _ _ _ = _,
  conv_rhs {rw choose_preimage_spec _ a},
  apply incl_eq_incl _ _ _ (le_refl _),
  swap, simp,
  apply proj_ext,
  intros j,
  ext1,
  rw [← CompHaus.coe_comp_apply, proj_trans, CompHaus.coe_comp_apply],
  erw concrete_category.limit.mk_π,
  change _ + _ = _,
  rw [← CompHaus.coe_comp_apply, proj_trans, CompHaus.coe_comp_apply],
  dsimp [level],
  simp only [add_left_eq_self],
  change subtype.val _ = _,
  erw [aux, concrete_category.limit.mk_π],
  refl,
end

lemma add_assoc (a b c : cone_point_type G) : a + b + c = a + (b + c) :=
begin
  let e :=
    (choose_index G (a + b) + choose_index G c) ⊔ (choose_index G a + choose_index G (b + c)),
  apply incl_eq_incl _ _ _ (le_sup_left : _ ≤ e) (le_sup_right : _ ≤ e),
  apply proj_ext,
  intros j,
  ext1,
  rw [← CompHaus.coe_comp_apply, proj_trans, CompHaus.coe_comp_apply],
  dsimp [level],
  erw concrete_category.limit.mk_π,
  rw [← CompHaus.coe_comp_apply, proj_trans, CompHaus.coe_comp_apply],
  dsimp [level],
  erw concrete_category.limit.mk_π,
  change subtype.val _ + subtype.val _ = subtype.val _ + subtype.val _,
  erw aux,
  dsimp,
  change _ = subtype.val _ + subtype.val _,
  conv_rhs { congr, skip, erw aux },
  erw concrete_category.limit.mk_π,
  erw concrete_category.limit.mk_π,
  erw add_assoc,
  refl,
end

lemma add_comm (a b : cone_point_type G) : a + b = b + a :=
begin
  change incl _ _ _ = incl _ _ _,
  apply incl_eq_incl _ _ _ (le_refl _) (le_of_eq _),
  swap, {rw add_comm},
  apply proj_ext,
  intros j,
  ext1,
  rw [← CompHaus.coe_comp_apply, proj_trans, CompHaus.coe_comp_apply],
  dsimp [level],
  erw concrete_category.limit.mk_π,
  rw [← CompHaus.coe_comp_apply, proj_trans, CompHaus.coe_comp_apply],
  dsimp [level],
  erw concrete_category.limit.mk_π,
  change _ + _ = _ + _,
  rw add_comm,
end

lemma add_left_neg (a : cone_point_type G) : -a + a = 0 :=
begin
  change incl _ _ _ = incl _ _ _,
  apply incl_eq_incl _ _ _ (le_refl _),
  swap, { simp },
  apply proj_ext,
  intros j,
  ext1,
  rw [← CompHaus.coe_comp_apply, proj_trans, CompHaus.coe_comp_apply],
  dsimp [level],
  erw concrete_category.limit.mk_π,
  rw [← CompHaus.coe_comp_apply, proj_trans, CompHaus.coe_comp_apply],
  dsimp [level],
  change subtype.val _ + subtype.val _ = _,
  erw aux,
  convert add_left_neg _,
  erw concrete_category.limit.mk_π, refl,
  erw concrete_category.limit.mk_π, refl,
end

instance : add_comm_group (cone_point_type G) :=
{ add_assoc := add_assoc G,
  zero_add := zero_add G,
  add_zero := by { intro a, rw [add_comm G, zero_add G] },
  add_left_neg := add_left_neg G,
  add_comm := add_comm G,
  ..(infer_instance : has_add _),
  ..(infer_instance : has_neg _),
  ..(infer_instance : has_zero _) }

def equiv (c : ℝ≥0) : cone_point_type_filt G c ≃ set.range (incl G c) :=
equiv.of_bijective (λ x, ⟨incl G c x, x, rfl⟩)
begin
  split,
  { intros x y h,
    apply incl_injective,
    apply_fun (λ e, e.1) at h,
    exact h },
  { rintro ⟨-,x,rfl⟩, use x }
end

instance (c : ℝ≥0) : topological_space (set.range (incl G c)) :=
topological_space.induced (equiv G c).symm infer_instance

def homeo (c : ℝ≥0) : set.range (incl G c) ≃ₜ cone_point_type_filt G c :=
homeomorph.homeomorph_of_continuous_open (equiv G c).symm (continuous_induced_dom)
begin
  intros U hU,
  have : inducing (equiv G c).symm := ⟨rfl⟩,
  rw this.is_open_iff at hU,
  obtain ⟨U,hU,rfl⟩ := hU,
  simpa,
end

instance (c : ℝ≥0) : t2_space (set.range (incl G c)) := (homeo G c).symm.t2_space

instance (c : ℝ≥0) : compact_space (set.range (incl G c)) := (homeo G c).symm.compact_space

instance : comphaus_filtered_pseudo_normed_group (cone_point_type G) :=
{ --to_add_comm_group := _,
  filtration := λ r, set.range (incl G r),
  filtration_mono := begin
    rintros a b h x ⟨x,rfl⟩,
    use trans G h x,
    rw incl_trans_apply,
  end,
  zero_mem_filtration := begin
    intros c,
    change incl _ _ _ ∈ _,
    use trans G (by simp : 0 ≤ c) 0,
    rw incl_trans_apply,
  end,
  neg_mem_filtration := begin
    rintros c x ⟨y,rfl⟩,
    use -y,
    change _ = incl _ _ _,
    apply incl_eq_incl _ _ _ (le_max_left _ _) (le_max_right _ _),
    apply proj_ext,
    intros j,
    rw [← CompHaus.coe_comp_apply, proj_trans, CompHaus.coe_comp_apply],
    dsimp [level],
    erw concrete_category.limit.mk_π,
    rw [← CompHaus.coe_comp_apply, proj_trans, CompHaus.coe_comp_apply],
    dsimp [level],
    erw concrete_category.limit.mk_π,
    ext1,
    dsimp,
    change _ = -(subtype.val _),
    erw aux,
    refl,
  end,
  add_mem_filtration := begin
    rintros c₁ c₂ x₁ x₂ ⟨x₁,rfl⟩ ⟨x₂,rfl⟩,
    use cone_point_type_filt_add G x₁ x₂,
    apply incl_eq_incl _ _ _ (le_max_left _ _) (le_max_right _ _),
    apply proj_ext,
    intros j,
    rw [← CompHaus.coe_comp_apply, proj_trans, CompHaus.coe_comp_apply],
    dsimp [level],
    erw concrete_category.limit.mk_π,
    rw [← CompHaus.coe_comp_apply, proj_trans, CompHaus.coe_comp_apply],
    dsimp [level],
    erw concrete_category.limit.mk_π,
    ext1,
    dsimp,
    change _ + _ = subtype.val _ + subtype.val _,
    erw [aux, aux],
    refl,
  end,
  topology := by apply_instance,
  t2 := by apply_instance,
  compact := by apply_instance,
  continuous_add' := sorry,
  continuous_neg' := sorry,
  continuous_cast_le := sorry }

-- This is the goal of this section...
instance : has_limits CompHausFiltPseuNormGrp₁ := sorry

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

attribute [derive [has_coe_to_sort, large_category, concrete_category]] ProFiltPseuNormGrp

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

namespace ProFiltPseuNormGrpWithTinv

variables (r' : ℝ≥0)

instance bundled_hom : bundled_hom (@profinitely_filtered_pseudo_normed_group_with_Tinv_hom r') :=
⟨@profinitely_filtered_pseudo_normed_group_with_Tinv_hom.to_fun r',
 @profinitely_filtered_pseudo_normed_group_with_Tinv_hom.id r',
 @profinitely_filtered_pseudo_normed_group_with_Tinv_hom.comp r',
 @profinitely_filtered_pseudo_normed_group_with_Tinv_hom.coe_inj r'⟩

attribute [derive [has_coe_to_sort, large_category, concrete_category]] ProFiltPseuNormGrpWithTinv

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
      dsimp at this, simpa only [prod.mk.eta, equiv.apply_symm_apply] using this, },
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
