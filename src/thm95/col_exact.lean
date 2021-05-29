import category_theory.products.basic

import for_mathlib.arrow.iso_mk
import for_mathlib.Cech.adjunction
import for_mathlib.simplicial.iso
import for_mathlib.wide_pullback

import polyhedral_lattice.cosimplicial_extra

import prop_92.prop_92
import normed_snake_dual
import thm95.double_complex
import thm95.col_exact_prep
import thm95.polyhedral_iso
import thm95.pfpng_iso

noncomputable theory

open_locale nnreal big_operators nat
open category_theory opposite simplex_category
local attribute [instance] type_pow

universe variables u u₀ uₘ
-- set_option pp.universes true

namespace thm95

variables (BD : breen_deligne.data) (c_ : ℕ → ℝ≥0) [BD.suitable c_]
variables (r r' : ℝ≥0) [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r' < 1)]
variables (V : SemiNormedGroup.{u})
variables (Λ : PolyhedralLattice.{u}) (M : ProFiltPseuNormGrpWithTinv.{u} r')
variables (N : ℕ) [fact (0 < N)] (n : ℕ)

-- move this
instance fact_le_of_lt (c₁ c₂ : ℝ≥0) [h : fact (c₁ < c₂)] : fact (c₁ ≤ c₂) := ⟨h.1.le⟩

@[simps obj map]
def scale_factorial : system_of_complexes.{u} ⥤ system_of_complexes.{u} :=
(whiskering_right _ _ _).obj $
homological_complex.modify_functor
  (λ m, SemiNormedGroup.rescale m!) (λ m₁ m₂, SemiNormedGroup.scale _ _)
.

namespace scale_factorial
open system_of_complexes SemiNormedGroup homological_complex

lemma is_weak_bounded_exact {C : system_of_complexes} {k K : ℝ≥0} [fact (1 ≤ k)] {m : ℕ} {c₀ : ℝ≥0}
  (hC : C.is_weak_bounded_exact k K m c₀) :
  (scale_factorial.obj C).is_weak_bounded_exact k (K * (m + 1)) m c₀ :=
begin
  intros c hc i hi x ε hε,
  let δ := ε * i!,
  have hδ : 0 < δ := mul_pos hε (nat.cast_pos.2 (nat.factorial_pos i)),
  have hifact : ¬(↑(i!) : ℝ) = 0 := by exact_mod_cast nat.factorial_ne_zero _,
  have him : 1 ≤ (↑m + 1) * ((↑i : ℝ) + 1)⁻¹,
  { refine le_trans _ (mul_le_mul_of_nonneg_right (show (↑i : ℝ) + 1 ≤ (↑m + 1),
      by rwa [add_le_add_iff_right, nat.cast_le])
      (inv_nonneg.2 (add_nonneg ((@nat.cast_nonneg ℝ _ i)) zero_le_one))),
    rw mul_inv_cancel (ne_of_lt (add_pos_of_nonneg_of_pos (@nat.cast_nonneg ℝ _ i) zero_lt_one)).symm },
  obtain ⟨_, _, rfl, rfl, y, hy⟩ := hC c hc i hi ((of_rescale i!).app _ x) δ hδ,
  refine ⟨_, _, rfl, rfl, ((SemiNormedGroup.to_rescale (i - 1)!).app _ y), _⟩,
  erw [rescale.norm_def, rescale.norm_def],
  simp only [nnreal.coe_nat_cast, nnreal.coe_add, nat.cast_succ, nat.factorial_succ,
    nat.cast_mul, nnreal.coe_one, nnreal.coe_mul, div_eq_mul_inv],
  rw [mul_inv_le_iff], swap, { exact_mod_cast nat.factorial_pos i },
  refine hy.trans _,
  rw [left_distrib, mul_inv', ← mul_assoc ↑i!, mul_comm ↑i!, mul_assoc _ ↑i!, mul_comm ↑i!,
    mul_assoc _ _ ↑i!, inv_mul_cancel_right' hifact, mul_comm _ ε, add_le_add_iff_right,
    mul_assoc ↑K],
  refine mul_le_mul_of_nonneg_left _ (nnreal.coe_nonneg _),
  rw [mul_comm _ ((↑i : ℝ) + 1)⁻¹, ← mul_assoc],
  refine le_trans (le_mul_of_one_le_left (by simp only [one_mul, norm_nonneg]) him)
    (mul_le_mul_of_nonneg_left _ (mul_nonneg (add_nonneg (nat.cast_nonneg m) zero_le_one)
    (inv_nonneg.2 (add_nonneg (nat.cast_nonneg i) zero_le_one)))),
  simpa using le_refl _
end

end scale_factorial

section
open PolyhedralLattice

def CLCFP' : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ ⥤ ℝ≥0ᵒᵖ ⥤ SemiNormedGroup :=
(ProFiltPseuNormGrpWithTinv.Pow r' n ⋙ (_root_.Filtration r').flip).op ⋙
  functor.op_hom _ _ ⋙ (whiskering_right ℝ≥0ᵒᵖ Profiniteᵒᵖ _).obj (CLC V)

lemma CLCFP'_map_app {M₁ M₂ : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ} (f : M₁ ⟶ M₂) (c : ℝ≥0ᵒᵖ) :
  ((CLCFP' r' V n).map f).app c = (CLCFP V r' c.unop n).map f := rfl

lemma CLCFP'_obj_map (M₁ : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ) (c₁ c₂ : ℝ≥0ᵒᵖ) (h : c₁ ⟶ c₂) :
  ((CLCFP' r' V n).obj M₁).map h =
    (by haveI : fact (c₂.unop ≤ c₁.unop) := ⟨le_of_hom h.unop⟩;
      exact (CLCFP.res V r' c₁.unop c₂.unop n).app M₁) :=
rfl

def Cech_nerve' : cosimplicial_object.augmented (ℝ≥0ᵒᵖ ⥤ SemiNormedGroup) :=
(cosimplicial_object.augmented.whiskering_obj.{u} _ _ (CLCFP' r' V n)).obj
  (Cech_nerve r' Λ M N)

lemma Cech_nerve'_hom_zero :
  (Cech_nerve'.{u} r' V Λ M N n).hom.app (mk.{u} 0) =
    (CLCFP' r' V n).map (Cech_augmentation_map.{u} r' Λ M N).op :=
begin
  dsimp only [Cech_nerve', cosimplicial_object.augmented.whiskering_obj],
  simp only [whisker_right_app, category.id_comp, functor.right_op_map, nat_trans.comp_app,
    functor.const_comp_inv_app, Cech_nerve_hom_zero],
end

@[simps obj map]
def Cech_nerve_level : ℝ≥0 ⥤ simplicial_object.augmented Profinite.{u} :=
(ProFiltPseuNormGrpWithTinv.Pow r' n ⋙ (Filtration r').flip).flip ⋙
  (simplicial_object.augmented.whiskering _ _).flip.obj (Cech_nerve.{u} r' Λ M N).left_op
.

lemma Cech_nerve_level_left_map (c : ℝ≥0) (i j : simplex_categoryᵒᵖ) (g : i ⟶ j) :
  ((Cech_nerve_level r' Λ M N n).obj c).left.map g =
    ((Filtration r').obj c).map ((ProFiltPseuNormGrpWithTinv.Pow r' n).map
      ((Hom M).map ((Cech_conerve (Λ.diagonal_embedding N)).map g.unop).op)) :=
rfl

lemma Cech_nerve_level_left_map' (c : ℝ≥0) (i j : simplex_categoryᵒᵖ) (g : i ⟶ j)
  (x : ((Cech_nerve_level r' Λ M N n).obj c).left.obj i) (k : fin n) :
  (((Cech_nerve_level r' Λ M N n).obj c).left.map g x).1 k =
    add_monoid_hom.comp (x.1 k) (polyhedral_lattice.conerve.map
      (Λ.diagonal_embedding N) ⇑(hom.to_preorder_hom g.unop)).to_add_monoid_hom :=
rfl

lemma Cech_nerve_level_hom_app (c : ℝ≥0) :
  ((Cech_nerve_level r' Λ M N n).obj c).hom.app (op (mk 0)) =
    ((Filtration r').obj c).map
      ((ProFiltPseuNormGrpWithTinv.Pow r' n).map (Cech_augmentation_map r' Λ M N)) :=
begin
  dsimp only [Cech_nerve_level_obj, nat_trans.comp_app, whisker_right_app,
    functor.const_comp_hom_app],
  erw [category.comp_id],
  dsimp only [nat_trans.left_op_app, unop_op],
  rw [Cech_nerve_hom_zero],
  dsimp only [functor.flip_obj_map, functor.comp_map, quiver.hom.unop_op,
    functor.flip_map_app],
  refl
end

@[simps X d]
def col_complex_aux : cochain_complex (ℝ≥0ᵒᵖ ⥤ SemiNormedGroup) ℕ :=
(Cech_nerve' r' V Λ M N n).to_cocomplex
.

@[simps obj map]
def col_complex_level : system_of_complexes :=
((whiskering_right _ _ _).obj $ FLC_functor' V).obj (Cech_nerve_level r' Λ M N n).op
.

@[simps obj map]
def col_complex : system_of_complexes :=
(col_complex_aux r' V Λ M N n).as_functor
.

def col_complex_level_iso_obj_X (c : ℝ≥0ᵒᵖ) :
  Π (i : ℕ), ((col_complex_level r' V Λ M N n).obj c).X i ≅ ((col_complex r' V Λ M N n).obj c).X i
| 0     := iso.refl _
| (i+1) := iso.refl _

lemma col_complex_level_iso_obj_comm (c : ℝ≥0ᵒᵖ) (i : ℕ) :
  (col_complex_level_iso_obj_X r' V Λ M N n c i).hom ≫
    ((col_complex r' V Λ M N n).obj c).d i (i + 1) =
  ((col_complex_level r' V Λ M N n).obj c).d i (i + 1) ≫
    (col_complex_level_iso_obj_X r' V Λ M N n c (i + 1)).hom :=
begin
  cases i,
  all_goals {
    dsimp only [col_complex_level_iso_obj_X],
    simp only [iso.refl_hom, category.id_comp, category.comp_id],
    dsimp only [col_complex_obj, col_complex_level_obj,
      cosimplicial_object.augmented.cocomplex,
      cosimplicial_object.augmented.to_cocomplex_d_2,
      cosimplicial_object.augmented.to_cocomplex_d,
      functor.const_comp_hom_app, functor.const_comp_inv_app,
      nat_trans.comp_app, whisker_right_app, nat_trans.right_op_app, nat_trans.left_op_app,
      cosimplicial_object.augmented.drop_obj, cosimplicial_object.coboundary,
      cosimplicial_object.δ, cosimplicial_object.whiskering_obj_obj_map],
    rw [dif_pos rfl, eq_to_hom_refl, category.comp_id,
        dif_pos rfl, eq_to_hom_refl, category.comp_id], },
  { erw [Cech_nerve'_hom_zero, Cech_nerve_hom_zero, SemiNormedGroup.LCC_obj_map',
      category.id_comp, category.comp_id],
    refl },
  { simp only [nat_trans.app_sum, nat_trans.app_gsmul],
    apply fintype.sum_congr, intro j, congr' 1,
    rw [SemiNormedGroup.LCC_obj_map'],
    refl, }
end

def col_complex_level_iso_obj (c : ℝ≥0ᵒᵖ) :
  (col_complex_level r' V Λ M N n).obj c ≅ (col_complex r' V Λ M N n).obj c :=
homological_complex.iso_of_components (col_complex_level_iso_obj_X r' V Λ M N n c)
(by { rintro i j (rfl : i + 1 = j), apply col_complex_level_iso_obj_comm })

lemma col_complex_level_iso_comm (c₁ c₂ : ℝ≥0ᵒᵖ) (h : c₁ ⟶ c₂) (i : ℕ) :
  ((col_complex_level r' V Λ M N n).map h ≫ (col_complex_level_iso_obj r' V Λ M N n c₂).hom).f i =
    ((col_complex_level_iso_obj r' V Λ M N n c₁).hom ≫ (col_complex r' V Λ M N n).map h).f i :=
begin
  cases i,
  all_goals {
    dsimp only [col_complex_level_iso_obj, col_complex_level_iso_obj_X,
      homological_complex.comp_f, homological_complex.iso_of_components_hom_f, iso.refl_hom],
      rw [category.id_comp, category.comp_id],
    dsimp only [col_complex_level_map, col_complex_map, whisker_right_app,
      cosimplicial_object.augmented.cocomplex,
      cosimplicial_object.augmented.point_map,
      cosimplicial_object.augmented.drop_map],
      rw [SemiNormedGroup.LCC_obj_map'], refl },
end

def col_complex_level_iso :
  col_complex_level r' V Λ M N n ≅ col_complex r' V Λ M N n :=
nat_iso.of_components (col_complex_level_iso_obj r' V Λ M N n)
(by { intros c₁ c₂ h, ext i : 2, apply col_complex_level_iso_comm })

lemma col_complex_level_iso_strict (c : ℝ≥0ᵒᵖ) (i : ℕ) :
  isometry (((col_complex_level_iso r' V Λ M N n).hom.app c).f i) :=
by { cases i; exact isometry_id }

def aug_map :=
((ProFiltPseuNormGrpWithTinv.Pow r' n).map (Cech_augmentation_map r' Λ M N))
  .to_profinitely_filtered_pseudo_normed_group_hom

section open profinitely_filtered_pseudo_normed_group_with_Tinv_hom
lemma aug_map_strict : (aug_map r' Λ M N n).strict :=
to_profinitely_filtered_pseudo_normed_group_hom_strict _
end

section open category_theory.simplicial_object simplicial_object

@[simps left right]
def Cech_nerve_level_hom' (c : ℝ≥0) :
  augmented.to_arrow.obj ((Cech_nerve_level r' Λ M N n).obj c) ⟶
    FLC_complex_arrow _ (aug_map_strict r' Λ M N n) c :=
@arrow.hom_mk _ _
  (augmented.to_arrow.obj ((Cech_nerve_level r' Λ M N n).obj c))
  (FLC_complex_arrow _ (aug_map_strict r' Λ M N n) c)
  (𝟙 _) (𝟙 _)
begin
  erw [category.comp_id, category.id_comp, augmented.to_arrow_obj_hom],
  dsimp only [Cech_nerve_level_obj, nat_trans.comp_app, whisker_right_app,
    functor.const_comp_hom_app, nat_trans.left_op_app, unop_op,
    functor.flip_obj_map, functor.comp_map, functor.flip_map_app],
  erw [category.comp_id, Cech_nerve_hom_zero],
  refl,
end

@[simps left right]
def Cech_nerve_level_inv' (c : ℝ≥0) :
  FLC_complex_arrow _ (aug_map_strict r' Λ M N n) c ⟶
    augmented.to_arrow.obj ((Cech_nerve_level r' Λ M N n).obj c) :=
@arrow.hom_mk _ _
  (FLC_complex_arrow _ (aug_map_strict r' Λ M N n) c)
  (augmented.to_arrow.obj ((Cech_nerve_level r' Λ M N n).obj c))
  (𝟙 _) (𝟙 _)
begin
  erw [category.comp_id, category.id_comp, augmented.to_arrow_obj_hom],
  dsimp only [Cech_nerve_level_obj, nat_trans.comp_app, whisker_right_app,
    functor.const_comp_hom_app, nat_trans.left_op_app, unop_op,
    functor.flip_obj_map, functor.comp_map, functor.flip_map_app],
  erw [category.comp_id, Cech_nerve_hom_zero],
  refl,
end

@[simps left right]
def Cech_nerve_level_hom (c : ℝ≥0) :
  (Cech_nerve_level r' Λ M N n).obj c ⟶
    (FLC_complex_arrow _ (aug_map_strict r' Λ M N n) c).augmented_cech_nerve :=
equivalence_left_to_right _ _ $ Cech_nerve_level_hom' _ _ _ _ _ _
.

lemma Cech_nerve_level_hom_injective' (c : ℝ≥0) (i : simplex_categoryᵒᵖ)
  (x y: ((((Cech_nerve_level r' Λ M N n).obj c).left.obj i)))
  (h : ∀ (j : ulift (fin ((unop i).len + 1))),
    (((Cech_nerve_level r' Λ M N n).obj c).left.map ((unop i).const j.down).op) x =
    (((Cech_nerve_level r' Λ M N n).obj c).left.map ((unop i).const j.down).op) y) : x = y :=
begin
  ext j : 2,
  let π := (polyhedral_lattice.conerve.π
    (Λ.diagonal_embedding N) (i.unop.len + 1)).to_add_monoid_hom,
  have hπ : function.surjective π := polyhedral_lattice.conerve.π_surjective _ _,
  rw ← add_monoid_hom.cancel_right hπ, -- Bingo!
  apply finsupp.add_hom_ext',
  intro k, specialize h ⟨k⟩,
  rw subtype.ext_iff at h,
  replace h := congr_fun h j,
  rw add_monoid_hom.ext_iff at h ⊢,
  intro l, specialize h ((Cech_conerve.obj_zero_iso _).inv l),
  dsimp only [Cech_nerve_level_obj, Cech_nerve_level_map,
    whiskering_obj_obj_map, functor.flip_obj_map, functor.flip_map_app,
    functor.comp_map, functor.left_op_map, quiver.hom.unop_op,
    Cech_nerve, cosimplicial_object.augmented.whiskering_obj, cosimplicial_object.whiskering,
    whiskering_right_obj_obj, whiskering_right_obj_map,
    functor.right_op_map, unop_op,
    cosimplicial_object.augmented.drop_obj, cosimplicial_object.augmented.drop_map,
    augmented_cosimplicial, augmented_Cech_conerve,
    cosimplicial_object.augment_right, Cech_conerve_map,
    Filtration_obj_map_to_fun, ProFiltPseuNormGrpWithTinv.Pow_map,
    Hom_obj, Hom_map_to_fun, polyhedral_lattice.Hom,
    profinitely_filtered_pseudo_normed_group_with_Tinv_hom.level,
    profinitely_filtered_pseudo_normed_group_with_Tinv.pi_map_to_fun,
    profinitely_filtered_pseudo_normed_group_with_Tinv.pi_lift_to_fun,
    profinitely_filtered_pseudo_normed_group_with_Tinv_hom.comp_to_fun,
    pseudo_normed_group.level, finsupp.single_add_hom_apply,
    subtype.coe_mk, add_monoid_hom.coe_mk_from_pi, add_monoid_hom.comp_apply] at h ⊢,
  erw [Cech_conerve.map_const_obj_zero_iso] at h,
  exact h,
end
.

lemma Cech_nerve_level_hom_injective (c : ℝ≥0) (i : simplex_categoryᵒᵖ) :
  function.injective ⇑((Cech_nerve_level_hom r' Λ M N n c).left.app i) :=
begin
  let F := FLC_complex_arrow _ (aug_map_strict r' Λ M N n) c,
  intros x y h,
  rw Profinite.wide_pullback.ext_iff' at h,
  have aux := λ j, (augmented_cech_nerve.left_map_comp_obj_zero_iso F i.unop j).symm,
  dsimp only [unop_op] at aux,
  simp only [← comp_apply, aux] at h,
  have aux' := (Cech_nerve_level_hom r' Λ M N n c).left.naturality,
  simp only [← category.assoc, ← aux'] at h, clear aux aux',
  simp only [category.assoc, Cech_nerve_level_hom, augmented_cech_nerve.left_obj_zero_iso_hom,
    equivalence_left_to_right_left_app_zero_comp_π, Cech_nerve_level_hom'_left,
    coe_comp, function.comp, id_apply] at h,
  apply Cech_nerve_level_hom_injective',
  exact h
end
.

namespace Cech_nerve_level_hom

/-! The goal is to build a section to `Cech_nerve_level_hom` -/

variables {r' Λ M N n}
variables {c : ℝ≥0} {i : simplex_category.{u}ᵒᵖ}
variables (y : (FLC_complex_arrow _ (aug_map_strict r' Λ M N n) c).augmented_cech_nerve.left.obj i)

def z₀' := limits.wide_pullback.base
(λ _, (FLC_complex_arrow _ (aug_map_strict r' Λ M N n) c).hom) y

def z' := λ j, limits.wide_pullback.π
(λ _, (FLC_complex_arrow _ (aug_map_strict r' Λ M N n) c).hom) j y

lemma hz' : ∀ j, ((FLC_complex_arrow _ (aug_map_strict r' Λ M N n) c).hom (z' y j)) = z₀' y :=
begin
  intro j,
  dsimp only [z₀', z'],
  rw [← comp_apply, limits.wide_pullback.π_arrow],
end

def z₀ := (Cech_nerve_level_inv' r' Λ M N n c).right (z₀' y)

def z := λ j, (Cech_nerve_level_inv' r' Λ M N n c).left (z' y j)

lemma hz : ∀ j, (augmented.to_arrow.obj ((Cech_nerve_level r' Λ M N n).obj c)).hom (z y j) = z₀ y :=
begin
  intro j, dsimp only [z₀, z],
  have := (Cech_nerve_level_inv' r' Λ M N n c).w,
  simp only [functor.id_map, augmented.to_arrow_obj_hom] at this,
  erw [← comp_apply, this, comp_apply, hz'],
  refl
end

def s' (y : (FLC_complex_arrow _ (aug_map_strict r' Λ M N n) c).augmented_cech_nerve.left.obj i) :
  (ProFiltPseuNormGrpWithTinv.Pow r' n).obj
    ((augmented.drop.obj (Cech_nerve r' Λ M N).left_op).obj i) :=
begin
  refine λ k,
    cosimplicial_lift Λ N _
      ((z₀ y).1 k)
      (λ j, add_monoid_hom.comp ((z y ⟨j⟩).1 k)
        (Cech_conerve.obj_zero_iso (Λ.diagonal_embedding N)).inv.to_add_monoid_hom) _,
  intros j l,
  dsimp only [add_monoid_hom.comp_apply, subtype.coe_mk,
    polyhedral_lattice_hom.coe_to_add_monoid_hom],
  rw [← hz y ⟨j⟩],
  dsimp only [augmented.to_arrow_obj_hom],
  rw [Cech_nerve_level_hom_app],
  dsimp only [Filtration_obj_map_to_fun, Cech_augmentation_map,
    profinitely_filtered_pseudo_normed_group_with_Tinv_hom.level,
    pseudo_normed_group.level,
    ProFiltPseuNormGrpWithTinv.Pow_map,
    profinitely_filtered_pseudo_normed_group_with_Tinv.pi_map_to_fun,
    cosimplicial_augmentation_map,
    Hom_map_to_fun, add_monoid_hom.comp_apply, subtype.coe_mk,
    polyhedral_lattice_hom.coe_to_add_monoid_hom, quiver.hom.unop_op,
    PolyhedralLattice.Cech_augmentation_map],
  refl,
end
.

def s (y : (FLC_complex_arrow _ (aug_map_strict r' Λ M N n) c).augmented_cech_nerve.left.obj i) :
  ((Cech_nerve_level r' Λ M N n).obj c).left.obj i :=
begin
  refine ⟨s' y, _⟩,
  intros k,
  apply cosimplicial_lift_mem_filtration,
  intros j c' l hl,
  dsimp only [add_monoid_hom.comp_apply, polyhedral_lattice_hom.coe_to_add_monoid_hom],
  apply (z y ⟨j⟩).property,
  rw [semi_normed_group.mem_filtration_iff] at hl ⊢,
  refine le_trans _ hl,
  exact (Cech_conerve.obj_zero_iso (Λ.diagonal_embedding N)).inv.strict l
end
.

lemma surjective (c : ℝ≥0) (i : simplex_categoryᵒᵖ) :
  function.surjective ⇑((Cech_nerve_level_hom r' Λ M N n c).left.app i) :=
begin
  intro y,
  refine ⟨Cech_nerve_level_hom.s y, _⟩,
  { rw Profinite.wide_pullback.ext_iff',
    intro j,
    erw [← augmented_cech_nerve.left_map_comp_obj_zero_iso _ _ j, ← comp_apply,
      ← category.assoc, ← (Cech_nerve_level_hom r' Λ M N n c).left.naturality,
      augmented_cech_nerve.left_map_comp_obj_zero_iso _ _ j, category.assoc],
    dsimp only [Cech_nerve_level_hom, augmented_cech_nerve.left_obj_zero_iso],
    erw [equivalence_left_to_right_left_app_zero_comp_π, Cech_nerve_level_hom'_left,
      category.comp_id],
    ext k : 2,
    have := Cech_nerve_level_left_map' r' Λ M N n c i _ (i.unop.const j.down).op,
    simp only [subtype.val_eq_coe] at this,
    erw this _ k, clear this,
    ext1 l',
    obtain ⟨l, rfl⟩ : ∃ l, quotient_add_group.mk l = l',
    { exact quotient.surjective_quotient_mk' l' },
    dsimp only [z₀, z, s', s, add_monoid_hom.comp_apply, subtype.coe_mk,
      polyhedral_lattice_hom.coe_to_add_monoid_hom,
      polyhedral_lattice.conerve.map_apply,
      add_monoid_hom.to_fun_eq_coe,
      polyhedral_lattice.conerve.map_add_hom_mk,
      cosimplicial_lift, polyhedral_lattice.conerve.lift'],
    refine (quotient_add_group.lift_mk'
      (polyhedral_lattice.conerve.L (Λ.diagonal_embedding N) ((unop i).len + 1)) _ _).trans _,
    dsimp only [finsupp.lift_add_hom_apply, finsupp.map_domain.add_monoid_hom_apply,
      unop_op],
    rw [finsupp.sum_map_domain_index_add_monoid_hom, finsupp.sum_eq_sum_fintype,
      fin.sum_univ_succ, finset.sum_eq_zero, add_zero],
    swap, { intros m hm, exfalso, change fin 0 at m, exact nat.not_lt_zero m m.2 },
    swap, { intro, rw add_monoid_hom.map_zero },
    dsimp only [add_monoid_hom.comp_apply, subtype.coe_mk,
      polyhedral_lattice_hom.coe_to_add_monoid_hom,
      Cech_nerve_level_inv'_left, Cech_conerve.obj_zero_iso,
      iso.trans_inv, subtype.val_eq_coe, quiver.hom.unop_op],
    rw [id_apply, comp_apply, Cech_conerve.obj_zero_iso'_inv,
      Cech_conerve.finsupp_fin_one_iso_inv],
    suffices : finsupp.single_add_hom 0 (l 0) = l,
    { cases j, rw this, refl },
    ext m o,
    change fin 1 at m,
    have hm : m = 0, { exact subsingleton.elim _ _ },
    simp only [hm, finsupp.single_add_hom_apply, finsupp.single_apply, if_pos rfl], }
end

end Cech_nerve_level_hom

instance Cech_nerve_level_hom_is_iso (c : ℝ≥0) : is_iso (Cech_nerve_level_hom r' Λ M N n c) :=
begin
  refine @simplicial_object.augmented.is_iso_of _ _ _ _ _ (id _) (id _),
  swap, { exact is_iso.id _ },
  intro i,
  apply Profinite.is_iso_of_bijective,
  exact ⟨Cech_nerve_level_hom_injective r' Λ M N n c i,
        Cech_nerve_level_hom.surjective c i⟩,
end

def Cech_nerve_level_iso (c : ℝ≥0) :
  (Cech_nerve_level r' Λ M N n).obj c ≅
    (FLC_complex_arrow _ (aug_map_strict r' Λ M N n) c).augmented_cech_nerve :=
as_iso (Cech_nerve_level_hom r' Λ M N n c)

def FLC_complex_aug_iso_obj (c : ℝ≥0ᵒᵖ) :
  (FLC_complex V _ (aug_map_strict r' Λ M N n)).obj c ≅ (col_complex_level r' V Λ M N n).obj c :=
(FLC_functor' V).map_iso (Cech_nerve_level_iso r' Λ M N n c.unop).op

def FLC_complex_aug_iso :
  FLC_complex V _ (aug_map_strict r' Λ M N n) ≅ col_complex_level r' V Λ M N n :=
nat_iso.of_components (FLC_complex_aug_iso_obj r' V Λ M N n)
begin
  intros c₁ c₂ h,
  dsimp only [FLC_complex, col_complex_level, FLC_functor, FLC_complex_aug_iso_obj,
    functor.comp_map, functor.map_iso_hom, whiskering_right_obj_obj,
    Cech_nerve_level_iso, iso.op_hom, as_iso_hom, functor.op_map],
  simp only [← category_theory.functor.map_comp, ← op_comp, quiver.hom.unop_op],
  congr' 2,
  apply simplicial_object.hom_ext,
  { dsimp only [unop_op],
    let f := FLC_complex_arrow _ (aug_map_strict r' Λ M N n) (unop c₁),
    rw ← cancel_mono (augmented_cech_nerve.left_obj_zero_iso f).hom,
    dsimp only [comma.comp_left, nat_trans.comp_app,
      Cech_nerve_level_hom, augmented_cech_nerve_map_left, cech_nerve_map_app,
      arrow.hom_mk_right, arrow.hom_mk_left, augmented_cech_nerve.left_obj_zero_iso_hom],
    simp only [category.assoc, limits.wide_pullback.lift_π,
      simplicial_object.equivalence_left_to_right_left_app_zero_comp_π],
    erw [← category.assoc, simplicial_object.equivalence_left_to_right_left_app_zero_comp_π],
    refl, },
  { dsimp only [equivalence_right_to_left_right, comma.comp_right, Cech_nerve_level_hom_right],
    erw [category.comp_id, category.id_comp],
    refl, }
end

end

lemma FLC_complex_aug_iso_strict (c : ℝ≥0ᵒᵖ) (i : ℕ) :
  isometry (((FLC_complex_aug_iso r' V Λ M N n).hom.app c).f i) :=
begin
  rw [← iso.app_hom, ← homological_complex.iso_app_hom],
  refine SemiNormedGroup.iso_isometry_of_norm_noninc _ _ _;
  [ rw [homological_complex.iso_app_hom, iso.app_hom],
    rw [homological_complex.iso_app_inv, iso.app_inv] ];
  { apply cosimplicial_object.augmented.cocomplex_map_norm_noninc;
    intros; apply SemiNormedGroup.LCC_obj_map_norm_noninc, },
end

def col_complex_obj_iso_X_zero (c : ℝ≥0ᵒᵖ) :
  ((col_complex r' V Λ M N n).obj c).X 0 ≅
    ((FLC_functor V).obj (op $ FLC_complex_arrow _ (aug_map_strict r' Λ M N n) (c.unop))).X 0 :=
iso.refl _

section
open profinitely_filtered_pseudo_normed_group

def FLC_arrow_iso_aux :
  ((ProFiltPseuNormGrpWithTinv.Pow r' n).obj
    (unop ((Cech_nerve r' Λ M N).right.obj (mk 0)))) ≅
  ProFiltPseuNormGrpWithTinv.of r' (rescale ↑N (((↥Λ →+ ↥M) ^ n) ^ N)) :=
(ProFiltPseuNormGrpWithTinv.Pow r' n).map_iso
    (Hom_cosimplicial_zero_iso Λ N r' M N rfl) ≪≫
  (ProFiltPseuNormGrpWithTinv.Pow_rescale_Pow_iso.{u u} r' N N n).app
    (polyhedral_lattice.Hom ↥Λ ↥M)
.

section open ProFiltPseuNormGrpWithTinv

lemma FLC_arrow_hom' {M₁ M₂ : ProFiltPseuNormGrpWithTinv r'} (f : M₁ ⟶ M₂) (c : ℝ≥0) :
  (FLC_complex_arrow f.to_profinitely_filtered_pseudo_normed_group_hom f.strict c).hom =
    ((Filtration r').obj c).map f :=
rfl

--move this
attribute [simps] linear_equiv.to_add_equiv

lemma FLC_arrow_iso_w (c : ℝ≥0) :
  ((((Filtration r').obj c).map_iso (FLC_arrow_iso_aux r' Λ M N n)).hom ≫
    (FLC_complex_arrow _ (sum_hom_strict ((↥Λ →+ ↥M) ^ n) N) c).hom : _) =
  ((FLC_complex_arrow _ (aug_map_strict r' Λ M N n) c).hom) :=
begin
  rw [← iso.eq_inv_comp],
  ext x i l,
  dsimp only [FLC_arrow_iso_aux, iso.trans_inv, functor.map_iso_inv, aug_map,
    Pow_rescale_Pow_iso, iso.app_inv, iso.symm_inv,
    nat_trans.comp_app, functor.associator_hom_app, functor.associator_inv_app,
    iso_whisker_left_inv, iso_whisker_right_inv, whisker_left_app, whisker_right_app,
    Pow_comm, Pow_rescale, FLC_arrow_hom'],
  erw [category.id_comp, category.id_comp, FLC_arrow_hom',
    ← ((Filtration r').obj c).map_comp, category.assoc, ← (Pow r' n).map_comp,
    Cech_augmentation_map_eq_Hom_sum],
  dsimp only [FLC_complex_arrow, arrow.mk_hom,
    Filtration_obj_map_to_fun, comp_apply,
    continuous_map.coe_mk, pseudo_normed_group.level, subtype.coe_mk,
    profinitely_filtered_pseudo_normed_group_with_Tinv_hom.to_profinitely_filtered_pseudo_normed_group_hom,
    profinitely_filtered_pseudo_normed_group_hom.mk_of_strict,
    profinitely_filtered_pseudo_normed_group_hom.mk_of_bound,
    profinitely_filtered_pseudo_normed_group_hom.coe_mk,
    add_monoid_hom.to_fun_eq_coe,
    profinitely_filtered_pseudo_normed_group_with_Tinv_hom.coe_to_add_monoid_hom,
    ProFiltPseuNormGrpWithTinv.Pow_map, nat_iso.of_components.hom_app, id,
    profinitely_filtered_pseudo_normed_group_with_Tinv_hom.level_coe],
  erw [comp_apply, comp_apply, iso_of_equiv_of_strict'_hom_apply],
  dsimp only [profinitely_filtered_pseudo_normed_group_with_Tinv.pi_map_to_fun,
    ProFiltPseuNormGrpWithTinv.Pow_mul_inv, Pow_comm, Pow_mul_comm,
    Pow_mul_comm_obj_hom_to_fun, Pow_mul_comm_obj_inv_to_fun,
    nat_iso.of_components.inv_app, Pow_rescale_aux_apply],
  simp only [comp_apply, rescale.of, equiv.refl_apply, equiv.refl_symm,
    nat_iso.of_components.inv_app, id, iso_of_equiv_of_strict'_inv_apply,
    rescale_map_to_fun, ProFiltPseuNormGrpWithTinv.Pow_mul_hom,
    equiv.symm_apply_apply, ProFiltPseuNormGrpWithTinv.Pow_Pow_X_hom_to_fun,
    ProFiltPseuNormGrpWithTinv.Pow_Pow_X_inv_to_fun,
    Pow_Pow_X_equiv_apply, Pow_Pow_X_equiv_symm_apply,
    Pow_mul_comm_obj_hom_to_fun, Pow_mul_comm_obj_inv_to_fun],
  rw [sum_hom_apply, Hom_sum_apply, finset.sum_apply],
  congr' 1,
  refine fintype.sum_congr _ _ _,
  intro j,
  simp only [Pow_Pow_X_equiv_apply, Pow_Pow_X_equiv_symm_apply,
    Pow_mul_comm_obj_hom_to_fun, Pow_mul_comm_obj_inv_to_fun,
    equiv.symm_trans_apply, equiv.symm_symm, equiv.curry_apply, equiv.curry_symm_apply,
    function.curry, function.uncurry, equiv.arrow_congr_symm, equiv.arrow_congr_apply,
    function.comp, equiv.refl_apply, equiv.refl_symm, equiv.trans_apply,
    linear_equiv.to_add_equiv_symm_apply, equiv.prod_comm_apply,
    linear_equiv.inv_fun_eq_symm, equiv.inv_fun_as_coe,
    linear_equiv.trans_apply, linear_equiv.symm_apply_apply, linear_equiv.symm_trans_apply,
    linear_map.fun_congr_left_symm, linear_map.fun_congr_left_apply, linear_map.fun_left_apply,
    equiv.symm_apply_apply, equiv.apply_symm_apply, equiv.prod_comm_symm],
  refl
end

end

def FLC_arrow_iso (c : ℝ≥0) :
  FLC_complex_arrow _ (aug_map_strict r' Λ M N n) c ≅
  FLC_complex_arrow _ (sum_hom_strict ((↥Λ →+ ↥M) ^ n) N) c :=
arrow.iso_mk (((Filtration r').obj c).map_iso (FLC_arrow_iso_aux r' Λ M N n)) (iso.refl _)
begin
  erw [functor.map_iso_hom, iso.refl_hom, category.comp_id],
  exact (FLC_arrow_iso_w r' Λ M N n c : _),
end

-- lemma FLC_arrow_iso_left_eq (c₁ c₂ : ℝ≥0) {_ : fact (c₁ ≤ c₂)}
--   (x : ((FLC_complex_arrow _ (aug_map_strict r' Λ M N n) c₁).left.to_Top)) :
--   pseudo_normed_group.cast_le (((FLC_arrow_iso r' Λ M N n c₁).hom.left) x) =
--     ((FLC_arrow_iso r' Λ M N n c₂).hom.left) (pseudo_normed_group.cast_le x) :=
-- by admit

-- lemma FLC_arrow_iso_right_eq (c₁ c₂ : ℝ≥0) {_ : fact (c₁ ≤ c₂)}
--   (x : ((FLC_complex_arrow _ (aug_map_strict r' Λ M N n) c₁).right.to_Top)) :
--   pseudo_normed_group.cast_le (((FLC_arrow_iso r' Λ M N n c₁).hom.right) x) =
--     ((FLC_arrow_iso r' Λ M N n c₂).hom.right) (pseudo_normed_group.cast_le x) :=
-- by admit

def col_complex_iso_obj (c : ℝ≥0ᵒᵖ) :
  (FLC_complex V _ (sum_hom_strict ((↥Λ →+ ↥M) ^ n) N)).obj c ≅
    (FLC_complex V _ (aug_map_strict r' Λ M N n)).obj c :=
begin
  refine (cosimplicial_object.augmented.cocomplex.map_iso _),
  refine functor.map_iso _ _,
  refine functor.map_iso _ _,
  refine functor.map_iso _ _,
  refine iso.op _,
  exact FLC_arrow_iso r' Λ M N n c.unop
end

def col_complex_iso_aux2 :
  FLC_complex V _ (sum_hom_strict ((↥Λ →+ ↥M) ^ n) N) ≅
  FLC_complex V _ (aug_map_strict r' Λ M N n) :=
nat_iso.of_components (col_complex_iso_obj r' V Λ M N n)
begin
  intros c₁ c₂ h,
  dsimp only [FLC_complex, FLC_functor, FLC_functor', col_complex_iso_obj, functor.comp_map,
    functor.map_iso_hom, iso.op_hom],
  simp only [← category_theory.functor.map_comp, ← op_comp],
  refl
end

section open cosimplicial_object

lemma col_complex_iso_aux2_strict (c : ℝ≥0ᵒᵖ) (i : ℕ) :
  isometry (((col_complex_iso_aux2 r' V Λ M N n).hom.app c).f i) :=
begin
  rw [← iso.app_hom, ← homological_complex.iso_app_hom],
  refine SemiNormedGroup.iso_isometry_of_norm_noninc _ _ _;
  [ rw [homological_complex.iso_app_hom, iso.app_hom],
    rw [homological_complex.iso_app_inv, iso.app_inv] ];
  { dsimp only [col_complex_iso_aux2, col_complex_iso_obj, nat_iso.of_components, functor.comp_map,
      functor.map_iso_hom, iso.op_hom, quiver.hom.unop_op, functor.op_map,
      cosimplicial_object.augmented.whiskering_obj_2,
      cosimplicial_object.augmented.whiskering_obj],
    apply augmented.cocomplex_map_norm_noninc;
    { intros, apply SemiNormedGroup.LCC_obj_map_norm_noninc, }, },
end

end

def col_complex_iso :
  FLC_complex V _ (sum_hom_strict ((↥Λ →+ ↥M)^n) N) ≅
  col_complex r' V Λ M N n :=
col_complex_iso_aux2 r' V Λ M N n ≪≫ FLC_complex_aug_iso r' V Λ M N n ≪≫ col_complex_level_iso r' V Λ M N n

lemma col_complex_iso_strict (c : ℝ≥0ᵒᵖ) (i : ℕ) :
  isometry (((col_complex_iso r' V Λ M N n).hom.app c).f i) :=
begin
  refine isometry.comp _ (col_complex_iso_aux2_strict r' V Λ M N n c i),
  exact (col_complex_level_iso_strict r' V Λ M N n c i).comp
    (FLC_complex_aug_iso_strict r' V Λ M N n c i),
end

end

lemma col_complex.is_weak_bounded_exact (d : ℝ≥0) [pseudo_normed_group.splittable ((Λ →+ M)^n) N d]
  (k : ℝ≥0) [fact (1 ≤ k)] (m : ℕ) (c₀ : ℝ≥0) (hdkc₀N : d ≤ (k - 1) * c₀ / N) :
  (col_complex r' V Λ M N n).is_weak_bounded_exact k 1 m c₀ :=
begin
  have key := FLC_complex.weak_bounded_exact V ((Λ →+ M)^n) N d k m c₀ hdkc₀N,
  exact key.of_iso _ (λ c, col_complex_iso_strict r' V Λ M N n (op c)),
end

@[simps obj map]
def col_complex_rescaled : system_of_complexes :=
scale_factorial.obj (col_complex r' V Λ M N n)
.

lemma col_complex_rescaled.is_weak_bounded_exact
  (d : ℝ≥0) [pseudo_normed_group.splittable ((Λ →+ M)^n) N d]
  (k : ℝ≥0) [fact (1 ≤ k)] (m : ℕ) (c₀ : ℝ≥0) (hdkc₀N : d ≤ (k - 1) * c₀ / N) :
  (col_complex_rescaled r' V Λ M N n).is_weak_bounded_exact k (m+1) m c₀ :=
begin
  have := scale_factorial.is_weak_bounded_exact
    (col_complex.is_weak_bounded_exact r' V Λ M N n d k m c₀ hdkc₀N),
  rwa [one_mul] at this,
end

end

namespace col_complex_rescaled

open polyhedral_lattice (Hom)
open PolyhedralLattice (cosimplicial)

instance move_pls (r' : ℝ≥0) (c : ℝ≥0ᵒᵖ) : fact (unop (r'.MulLeft.op.obj c) ≤ r' * unop c) :=
⟨le_rfl⟩

instance move_pls2 (c : ℝ≥0ᵒᵖ) : fact (unop (r'.MulLeft.op.obj c) ≤ unop c) :=
by { dsimp [nnreal.MulLeft], apply_instance }

def T_inv_sub_Tinv_f_succ [normed_with_aut r V] (c : ℝ≥0ᵒᵖ) (i : ℕ) :
  ((col_complex_rescaled.{u} r' V Λ M N n).obj c).X (i + 1) ⟶
    (((col_complex_rescaled.{u} r' V Λ M N n).scale_index_left r').obj c).X (i + 1) :=
(SemiNormedGroup.rescale (i+1)!).map $ (CLCFP.T_inv_sub_Tinv r r' V _ _ n).app _

def T_inv_sub_Tinv_f [normed_with_aut r V] (c : ℝ≥0ᵒᵖ) :
  Π i, ((col_complex_rescaled.{u} r' V Λ M N n).obj c).X i ⟶
  (((col_complex_rescaled.{u} r' V Λ M N n).scale_index_left r').obj c).X i
| 0     := (SemiNormedGroup.rescale 0!).map $ (CLCFP.T_inv_sub_Tinv r r' V _ _ n).app _
| (i+1) := T_inv_sub_Tinv_f_succ r r' V Λ M N n c i

section open system_of_complexes category_theory.preadditive category_theory.cosimplicial_object
  homological_complex

lemma T_inv_sub_Tinv_comm_zero [normed_with_aut r V] (c : ℝ≥0ᵒᵖ) :
  T_inv_sub_Tinv_f r r' V Λ M N n c 0 ≫
    (((col_complex_rescaled r' V Λ M N n).scale_index_left r').obj c).d 0 1 =
  ((col_complex_rescaled r' V Λ M N n).obj c).d 0 1 ≫
    T_inv_sub_Tinv_f r r' V Λ M N n c 1 :=
begin
  dsimp only [T_inv_sub_Tinv_f, T_inv_sub_Tinv_f_succ, scale_index_left, col_complex_rescaled],
  refine SemiNormedGroup.scale_comm _ _ _ _ _ _ _,
  dsimp,
  rw [if_pos rfl, category.comp_id],
  dsimp only [augmented.to_cocomplex_d],
  erw [Cech_nerve'_hom_zero],
  dsimp only [CLCFP'_map_app],
  erw nat_trans.naturality,
  refl
end
.

lemma T_inv_sub_Tinv_comm_succ [normed_with_aut r V] (c : ℝ≥0ᵒᵖ) (i : ℕ) :
  T_inv_sub_Tinv_f r r' V Λ M N n c (i+1) ≫
    (((col_complex_rescaled r' V Λ M N n).scale_index_left r').obj c).d (i+1) (i+2) =
  ((col_complex_rescaled r' V Λ M N n).obj c).d (i+1) (i+2) ≫
    T_inv_sub_Tinv_f r r' V Λ M N n c (i+2) :=
begin
  dsimp only [T_inv_sub_Tinv_f, T_inv_sub_Tinv_f_succ, scale_index_left, col_complex_rescaled],
  refine SemiNormedGroup.scale_comm _ _ _ _ _ _ _,
  dsimp,
  rw [if_pos rfl, category.comp_id],
  dsimp only [augmented.to_cocomplex_d, coboundary, augmented.drop_obj, Cech_nerve',
    augmented.whiskering_obj_2, augmented.whiskering_obj, cosimplicial_object.δ,
    whiskering_obj_obj_map],
  simp only [nat_trans.app_sum, nat_trans.app_gsmul, sum_comp, comp_sum, gsmul_comp, comp_gsmul],
  apply fintype.sum_congr,
  intro j,
  congr' 1,
  dsimp only [CLCFP'_map_app],
  erw nat_trans.naturality,
  refl,
end
.

lemma T_inv_sub_Tinv_naturality_zero [normed_with_aut r V] (c₁ c₂ : ℝ≥0ᵒᵖ) (h : c₁ ⟶ c₂) :
  ((col_complex_rescaled r' V Λ M N n).map h).f 0 ≫ T_inv_sub_Tinv_f r r' V Λ M N n c₂ 0 =
    T_inv_sub_Tinv_f r r' V Λ M N n c₁ 0 ≫
      (((col_complex_rescaled r' V Λ M N n).scale_index_left r').map h).f 0 :=
begin
  dsimp only [T_inv_sub_Tinv_f, scale_index_left, ScaleIndexLeft_obj_map,
    col_complex_rescaled, scale_factorial_obj, functor.comp_map, modify_functor_map_f,
    col_complex_map, augmented.to_cocomplex_obj, augmented.point_obj, Cech_nerve',
    augmented.whiskering_obj],
  simp only [← category_theory.functor.map_comp],
  congr' 1,
  dsimp only [CLCFP'_obj_map, CLCFP.T_inv_sub_Tinv, nnreal.MulLeft, functor.op_obj, unop_op],
  simp only [nat_trans.app_sub, comp_sub, sub_comp, ← nat_trans.comp_app],
  congr' 2,
  { rw [category.assoc, ← CLCFP.res_comp_T_inv],
    haveI : fact (c₂.unop ≤ c₁.unop) := ⟨le_of_hom h.unop⟩,
    simp only [← category.assoc, CLCFP.res_comp_res], },
  { dsimp only [CLCFP.Tinv, CLCFP.res, CLC, LC],
    simp only [← whisker_right_comp, ← nat_trans.op_comp],
    refl, }
end
.

lemma T_inv_sub_Tinv_naturality_succ [normed_with_aut r V] (c₁ c₂ : ℝ≥0ᵒᵖ) (h : c₁ ⟶ c₂) (i : ℕ) :
  ((col_complex_rescaled r' V Λ M N n).map h).f (i+1) ≫ T_inv_sub_Tinv_f r r' V Λ M N n c₂ (i+1) =
    T_inv_sub_Tinv_f r r' V Λ M N n c₁ (i+1) ≫
      (((col_complex_rescaled r' V Λ M N n).scale_index_left r').map h).f (i+1) :=
begin
  dsimp only [T_inv_sub_Tinv_f, T_inv_sub_Tinv_f_succ, scale_index_left, ScaleIndexLeft_obj_map,
    col_complex_rescaled, scale_factorial_obj, functor.comp_map, modify_functor_map_f,
    col_complex_map, augmented.to_cocomplex_obj, augmented.drop_obj, Cech_nerve',
    augmented.whiskering_obj, whiskering_obj_obj_obj],
  simp only [← category_theory.functor.map_comp],
  congr' 1,
  dsimp only [CLCFP'_obj_map, CLCFP.T_inv_sub_Tinv, nnreal.MulLeft, functor.op_obj, unop_op],
  simp only [nat_trans.app_sub, comp_sub, sub_comp],
  erw [← nat_trans.comp_app, ← nat_trans.comp_app, ← nat_trans.comp_app, ← nat_trans.comp_app],
  congr' 2,
  { rw [category.assoc, ← CLCFP.res_comp_T_inv],
    haveI : fact (c₂.unop ≤ c₁.unop) := ⟨le_of_hom h.unop⟩,
    simp only [← category.assoc, CLCFP.res_comp_res], },
  { dsimp only [CLCFP.Tinv, CLCFP.res, CLC, LC],
    simp only [← whisker_right_comp, ← nat_trans.op_comp],
    refl, }
end

end

def T_inv_sub_Tinv [normed_with_aut r V] :
  col_complex_rescaled r' V Λ M N n ⟶ (col_complex_rescaled r' V Λ M N n).scale_index_left r' :=
{ app := λ c,
  { f := T_inv_sub_Tinv_f r r' V Λ M N n c,
    comm' :=
    begin
      rintros i j (rfl : i + 1 = j),
      cases i, { apply T_inv_sub_Tinv_comm_zero }, { apply T_inv_sub_Tinv_comm_succ }
    end },
  naturality' :=
  begin
    intros c₁ c₂ h, ext i : 2, cases i,
    { apply T_inv_sub_Tinv_naturality_zero },
    { apply T_inv_sub_Tinv_naturality_succ },
  end }

def T_inv_sub_Tinv' (c : ℝ≥0) [normed_with_aut r V] :=
(system_of_complexes.ScaleIndexRight c).map
  (col_complex_rescaled.T_inv_sub_Tinv r r' V Λ M N n)

end col_complex_rescaled

namespace double_complex

open polyhedral_lattice (Hom)

local attribute [semireducible] CLCFPTinv CLCFPTinv₂ CLCFP -- CLCTinv

@[simps obj map]
def col'_aux [normed_with_aut r V] (n : ℕ) : system_of_complexes :=
(double_complex' BD c_ r r' V Λ M N).col n

@[simps obj map]
def col' [normed_with_aut r V] (n : ℕ) : system_of_complexes :=
scale_factorial.obj (col'_aux BD c_ r r' V Λ M N n)

def col_iso_obj_X [normed_with_aut r V] (c : ℝ≥0ᵒᵖ) :
  Π m, (((double_complex.{u} BD c_ r r' V Λ M N).col n).obj c).X m ≅
  ((col'.{u} BD c_ r r' V Λ M N n).obj c).X m
| 0     := (SemiNormedGroup.iso_rescale _).app _
| 1     := (SemiNormedGroup.iso_rescale _).app _
| (m+2) := iso.refl _

section

open homological_complex system_of_complexes

lemma col_iso_comm₁_0 [normed_with_aut r V] (c : ℝ≥0ᵒᵖ) :
  (col_iso_obj_X BD c_ r r' V Λ M N n c 0).hom ≫
    ((col' BD c_ r r' V Λ M N n).obj c).d 0 1 =
  (((double_complex BD c_ r r' V Λ M N).col n).obj c).d 0 1 ≫
    (col_iso_obj_X BD c_ r r' V Λ M N n c 1).hom :=
by { dsimp only [col_iso_obj_X], ext, refl }
.

lemma col_iso_comm₁_1 [normed_with_aut r V] (c : ℝ≥0ᵒᵖ) :
  (col_iso_obj_X BD c_ r r' V Λ M N n c 1).hom ≫
    ((col' BD c_ r r' V Λ M N n).obj c).d 1 2 =
  (((double_complex BD c_ r r' V Λ M N).col n).obj c).d 1 2 ≫
    (col_iso_obj_X BD c_ r r' V Λ M N n c 2).hom :=
begin
  delta col_iso_obj_X,
  simp only [iso.refl_hom, nat.rec_add_one, category.id_comp, category.comp_id,
    system_of_double_complexes.col_obj_d],
  dsimp only [col'_obj, col'_aux_obj, double_complex', double_complex,
    double_complex_aux_rescaled, as_functor_obj, modify_d, eval_obj, eval_map,
    functor.map_homological_complex_obj_d, functor.map_homological_complex_obj_X,
    nat_trans.comp_app, comp_f, rescale_functor, rescale_nat_trans,
    system_of_complexes.rescale, scale],
  refl
end
.

lemma col_iso_comm₂_0 [normed_with_aut r V] (c₁ c₂ : ℝ≥0ᵒᵖ) (h : c₁ ⟶ c₂) :
  (((double_complex.{u} BD c_ r r' V Λ M N).col n).map h).f 0 ≫
    (col_iso_obj_X BD c_ r r' V Λ M N n c₂ 0).hom =
  (col_iso_obj_X BD c_ r r' V Λ M N n c₁ 0).hom ≫
    ((col'.{u} BD c_ r r' V Λ M N n).map h).f 0 :=
by { dsimp only [col_iso_obj_X], ext, refl }
.

lemma col_iso_comm₂_1 [normed_with_aut r V] (c₁ c₂ : ℝ≥0ᵒᵖ) (h : c₁ ⟶ c₂) :
  (((double_complex.{u} BD c_ r r' V Λ M N).col n).map h).f 1 ≫
    (col_iso_obj_X BD c_ r r' V Λ M N n c₂ 1).hom =
  (col_iso_obj_X BD c_ r r' V Λ M N n c₁ 1).hom ≫
    ((col'.{u} BD c_ r r' V Λ M N n).map h).f 1 :=
by { dsimp only [col_iso_obj_X], ext, refl }
.

local attribute [irreducible] CLCFPTinv CLCFPTinv₂ CLCFP
  SemiNormedGroup.rescale SemiNormedGroup.scale
  double_complex_aux

lemma col_iso_comm₁_succ [normed_with_aut r V] (c : ℝ≥0ᵒᵖ) (i : ℕ) :
  (col_iso_obj_X BD c_ r r' V Λ M N n c i.succ.succ).hom ≫
    ((col'.{u} BD c_ r r' V Λ M N n).obj c).d i.succ.succ (i.succ.succ + 1) =
  (((double_complex.{u} BD c_ r r' V Λ M N).col n).obj c).d i.succ.succ (i.succ.succ + 1) ≫
    (col_iso_obj_X BD c_ r r' V Λ M N n c (i.succ.succ + 1)).hom :=
begin
  dsimp only [col_iso_obj_X, iso.refl_hom],
  simp only [category.id_comp, category.comp_id, system_of_double_complexes.col_obj_d],
  refl,
end
.

lemma col_iso_comm₂_succ [normed_with_aut r V] (c₁ c₂ : ℝ≥0ᵒᵖ) (h : c₁ ⟶ c₂) (i : ℕ) :
  (((double_complex.{u} BD c_ r r' V Λ M N).col n).map h).f (i+2) ≫
    (col_iso_obj_X BD c_ r r' V Λ M N n c₂ (i+2)).hom =
  (col_iso_obj_X BD c_ r r' V Λ M N n c₁ (i+2)).hom ≫
    ((col'.{u} BD c_ r r' V Λ M N n).map h).f (i+2) :=
begin
  dsimp only [col_iso_obj_X, iso.refl_hom],
  simp only [category.id_comp, category.comp_id, system_of_double_complexes.col_obj_d],
  refl
end

lemma col_iso_comm₂ [normed_with_aut r V] (c₁ c₂ : ℝ≥0ᵒᵖ) (h : c₁ ⟶ c₂) :
  ∀ i, (((double_complex.{u} BD c_ r r' V Λ M N).col n).map h).f i ≫
    (col_iso_obj_X BD c_ r r' V Λ M N n c₂ i).hom =
  (col_iso_obj_X BD c_ r r' V Λ M N n c₁ i).hom ≫
    ((col'.{u} BD c_ r r' V Λ M N n).map h).f i
| 0     := col_iso_comm₂_0 _ _ _ _ _ _ _ _ _ _ _ _
| 1     := col_iso_comm₂_1 _ _ _ _ _ _ _ _ _ _ _ _
| (i+2) := col_iso_comm₂_succ _ _ _ _ _ _ _ _ _ _ _ _ _
.

end

section

open homological_complex

-- set_option pp.universes true

@[simps]
def col_iso [normed_with_aut r V] :
  (double_complex.{u} BD c_ r r' V Λ M N).col n ≅
  col'.{u} BD c_ r r' V Λ M N n :=
nat_iso.of_components (λ c, iso_of_components (col_iso_obj_X.{u} BD c_ r r' V Λ M N n _)
  begin
    rintro i j (rfl : i + 1 = j),
    cases i, { exact col_iso_comm₁_0 BD c_ r r' V Λ M N n c, },
    cases i, { exact col_iso_comm₁_1 BD c_ r r' V Λ M N n c, },
    { exact col_iso_comm₁_succ BD c_ r r' V Λ M N n c i, },
  end)
  begin
    intros c₁ c₂ h, ext i : 2,
    dsimp only [comp_f, iso_of_components_hom_f],
    exact col_iso_comm₂ BD c_ r r' V Λ M N n c₁ c₂ h i,
  end
.

lemma col_iso_strict [normed_with_aut r V] (c : ℝ≥0ᵒᵖ) (i : ℕ) :
  isometry (iso_app ((col_iso BD c_ r r' V Λ M N n).app c) i).hom :=
begin
  dsimp only [iso_app_hom, nat_iso.app_hom, col_iso_hom_app_f],
  cases i, { delta col_iso_obj_X, apply SemiNormedGroup.iso_rescale_isometry, exact nat.cast_one },
  cases i, { delta col_iso_obj_X, apply SemiNormedGroup.iso_rescale_isometry, exact nat.cast_one },
  { delta col_iso_obj_X, exact isometry_id }
end

lemma col_iso_inv_strict [normed_with_aut r V] (c : ℝ≥0ᵒᵖ) (i : ℕ) :
  isometry (iso_app ((col_iso BD c_ r r' V Λ M N n).app c) i).inv :=
(col_iso_strict BD c_ r r' V Λ M N n c i).right_inv $
λ x, by rw [← comp_apply, iso.inv_hom_id, id_apply]

end

lemma col_obj_X_zero [normed_with_aut r V] (c : ℝ≥0ᵒᵖ) :
  (((double_complex BD c_ r r' V Λ M N).col n).obj c).X 0 =
  (CLCFPTinv r V r' (c.unop * c_ n) (BD.X n)).obj (op $ Hom Λ M) := rfl

-- local attribute [semireducible] opposite

def col_ι_f_succ [normed_with_aut r V] (c : ℝ≥0ᵒᵖ) (i : ℕ) :
  ((col'.{u} BD c_ r r' V Λ M N n).obj c).X (i+1) ⟶
    (((col_complex_rescaled.{u} r' V Λ M N (BD.X n)).scale_index_right (c_ n)).obj c).X (i+1) :=
(SemiNormedGroup.rescale (i+1)!).map (CLCTinv.ι r V _ _)

def col_ι_f [normed_with_aut r V] (c : ℝ≥0ᵒᵖ) :
  Π i, ((col'.{u} BD c_ r r' V Λ M N n).obj c).X i ⟶
    (((col_complex_rescaled.{u} r' V Λ M N (BD.X n)).scale_index_right (c_ n)).obj c).X i
| 0     := (SemiNormedGroup.rescale 0!).map (CLCTinv.ι r V _ _)
| (i+1) := col_ι_f_succ _ _ _ _ _ _ _ _ _ _ i

section open homological_complex system_of_complexes breen_deligne

lemma col_ι_f_comm_zero [normed_with_aut r V] (c : ℝ≥0ᵒᵖ) :
  col_ι_f BD c_ r r' V Λ M N n c 0 ≫
    (((col_complex_rescaled r' V Λ M N (BD.X n)).scale_index_right (c_ n)).obj c).d 0 1 =
  ((col' BD c_ r r' V Λ M N n).obj c).d 0 1 ≫ col_ι_f BD c_ r r' V Λ M N n c 1 :=
begin
  dsimp only [col_ι_f, col_ι_f_succ, col'_obj, functor.map_homological_complex_obj_d,
    modify_d, eval_map, scale_index_right, ScaleIndexRight_obj_obj, col_complex_rescaled_obj,
    scale'_app],
  refine SemiNormedGroup.scale_comm _ _ _ _ _ _ _,
  rw [dif_pos rfl, dif_pos rfl],
  simp only [cosimplicial_object.augmented.to_cocomplex_d, eq_to_hom_refl, category.comp_id],
  erw [Cech_nerve'_hom_zero, cosimplicial_system_of_complexes_hom_zero],
  dsimp only [data.system_map, data.complex, data.complex₂_map_f, CLCFPTinv₂, CLCTinv.F_map],
  symmetry,
  apply CLCTinv.map_comp_ι,
end

section open category_theory.preadditive

lemma col_ι_f_comm_succ [normed_with_aut r V] (c : ℝ≥0ᵒᵖ) (i : ℕ) :
  col_ι_f BD c_ r r' V Λ M N n c (i + 1) ≫
    (((col_complex_rescaled r' V Λ M N (BD.X n)).scale_index_right (c_ n)).obj c).d (i+1) (i+2) =
  ((col' BD c_ r r' V Λ M N n).obj c).d (i + 1) (i + 2) ≫ col_ι_f BD c_ r r' V Λ M N n c (i+2) :=
begin
  dsimp only [col_ι_f, col_ι_f_succ, col'_obj, functor.map_homological_complex_obj_d,
    modify_d, eval_map, scale_index_right, ScaleIndexRight_obj_obj, col_complex_rescaled_obj,
    scale'_app],
  refine SemiNormedGroup.scale_comm _ _ _ _ _ _ _,
  rw [dif_pos rfl, dif_pos rfl],
  simp only [cosimplicial_object.augmented.to_cocomplex_d, eq_to_hom_refl, category.comp_id,
    cosimplicial_object.coboundary, nat_trans.app_sum, nat_trans.app_gsmul,
    ← homological_complex.hom.f_add_monoid_hom_apply, add_monoid_hom.map_sum,
    add_monoid_hom.map_gsmul, sum_comp, comp_sum, gsmul_comp, comp_gsmul],
  symmetry,
  apply fintype.sum_congr,
  intro j,
  refl,
end

end

lemma col_ι_f_comm [normed_with_aut r V] (c : ℝ≥0ᵒᵖ) :
  ∀ i, col_ι_f BD c_ r r' V Λ M N n c i ≫
    (((col_complex_rescaled r' V Λ M N (BD.X n)).scale_index_right (c_ n)).obj c).d i (i + 1) =
  ((col' BD c_ r r' V Λ M N n).obj c).d i (i + 1) ≫ col_ι_f BD c_ r r' V Λ M N n c (i + 1)
| 0     := by apply col_ι_f_comm_zero
| (i+1) := by apply col_ι_f_comm_succ

section open category_theory.cosimplicial_object

lemma col_ι_naturality_zero [normed_with_aut r V] (c₁ c₂ : ℝ≥0ᵒᵖ) (h : c₁ ⟶ c₂) :
  ((col' BD c_ r r' V Λ M N n).map h).f 0 ≫ col_ι_f BD c_ r r' V Λ M N n c₂ 0 =
  col_ι_f BD c_ r r' V Λ M N n c₁ 0 ≫ (((col_complex_rescaled r' V Λ M N (BD.X n)).scale_index_right (c_ n)).map h).f 0 :=
begin
  dsimp only [col'_map, functor.map_homological_complex_map_f, eval_map,
    modify_functor_map_f, col_ι_f,
    scale_index_right, ScaleIndexRight_obj_map, col_complex_rescaled_map],
  simp only [← category_theory.functor.map_comp],
  congr' 1,
  dsimp only [augmented.to_cocomplex_obj, augmented.point_obj, cosimplicial_system_of_complexes,
    Cech_nerve', augmented.whiskering_obj, CLCFP',
    data.system_obj, data.complex, data.complex₂_obj_X, CLCFPTinv₂.res, CLCTinv.map_nat,
    functor.comp_obj, functor.comp_map, functor.op_obj, functor.op_map, whiskering_right_obj_obj,
    functor.op_hom_obj, unop_op, functor.flip_obj_map],
  apply CLCTinv.map_comp_ι,
end
.

lemma col_ι_naturality_succ [normed_with_aut r V] (c₁ c₂ : ℝ≥0ᵒᵖ) (h : c₁ ⟶ c₂) (i : ℕ) :
  ((col' BD c_ r r' V Λ M N n).map h).f (i+1) ≫ col_ι_f BD c_ r r' V Λ M N n c₂ (i+1) =
  col_ι_f BD c_ r r' V Λ M N n c₁ (i+1) ≫ (((col_complex_rescaled r' V Λ M N (BD.X n)).scale_index_right (c_ n)).map h).f (i+1) :=
begin
  dsimp only [col'_map, functor.map_homological_complex_map_f, eval_map,
    modify_functor_map_f, col_ι_f, col_ι_f_succ,
    scale_index_right, ScaleIndexRight_obj_map, col_complex_rescaled_map],
  simp only [← category_theory.functor.map_comp],
  congr' 1,
  dsimp only [augmented.to_cocomplex_obj, augmented.drop_obj, cosimplicial_system_of_complexes,
    Cech_nerve', augmented.whiskering_obj, CLCFP', whiskering_obj_obj_obj,
    data.system_obj, data.complex, data.complex₂_obj_X, CLCFPTinv₂.res, CLCTinv.map_nat,
    functor.comp_obj, functor.comp_map, functor.op_obj, functor.op_map, whiskering_right_obj_obj,
    functor.op_hom_obj, unop_op, functor.flip_obj_map],
  apply CLCTinv.map_comp_ι,
end
.

end

end

def col_ι [normed_with_aut r V] :
  col'.{u} BD c_ r r' V Λ M N n ⟶
    (col_complex_rescaled.{u} r' V Λ M N (BD.X n)).scale_index_right (c_ n) :=
{ app := λ c,
  { f := col_ι_f BD c_ r r' V Λ M N n c,
    comm' := by { rintro i j (rfl : i + 1 = j), apply col_ι_f_comm } },
  naturality' :=
  begin
    intros c₁ c₂ h, ext i : 2,
    cases i,
    { apply col_ι_naturality_zero },
    { apply col_ι_naturality_succ },
  end }

variables [normed_with_aut r V] (c : ℝ≥0ᵒᵖ) (i : ℕ)

lemma col_ι_range :
  (((double_complex.col_ι BD c_ r r' V Λ M N n).app c).f i).range =
  (((col_complex_rescaled.T_inv_sub_Tinv' r r' V Λ M N (BD.X n) (c_ n)).app c).f i).ker :=
begin
  cases i;
  { refine SemiNormedGroup.rescale_exact _ _ _ _,
    rw CLCTinv.ι_range',
    ext1 x,
    refl, },
end

lemma col_ι_isometry :
  isometry (((double_complex.col_ι BD c_ r r' V Λ M N n).app c).f i) :=
begin
  cases i;
  { refine SemiNormedGroup.rescale_map_isometry _ _,
    apply normed_group_hom.isometry_of_norm,
    intro, refl },
end

end double_complex

namespace col_complex_rescaled

lemma d_zero_norm_noninc (c : ℝ≥0) :
  (@system_of_complexes.d (col_complex_rescaled r' V Λ M N n) c 0 1).norm_noninc :=
begin
  refine ((SemiNormedGroup.scale_bound_by _ _ _).comp' (1:ℕ) _ 1 _ _).norm_noninc,
  { simp only [nat.factorial_zero, nat.factorial_one, nat.cast_one, div_one, mul_one], },
  apply SemiNormedGroup.rescale_map_bound_by,
  have : (1 : ℝ≥0) = ∑ i : fin 1, 1,
  { simp only [finset.card_fin, mul_one, finset.sum_const, nsmul_eq_mul, nat.cast_id,
      nat.cast_bit1, nat.cast_add, nat.cast_one] },
  dsimp [system_of_complexes.rescale_functor, double_complex_aux,
    cosimplicial_object.augmented.to_cocomplex_d],
  erw [category.comp_id, if_pos rfl, Cech_nerve'_hom_zero, zero_add],
  apply normed_group_hom.norm_noninc.bound_by_one,
  apply CLC.map_norm_noninc,
end

lemma d_succ_norm_noninc (c : ℝ≥0) (p : ℕ) :
  (@system_of_complexes.d (col_complex_rescaled r' V Λ M N n) c (p+1) (p+2)).norm_noninc :=
begin
  refine ((SemiNormedGroup.scale_bound_by _ _ _).comp' (p+2:ℕ) _ 1 _ _).norm_noninc,
  { rw [mul_comm, ← mul_div_assoc, eq_comm, ← nat.cast_mul, nat.factorial_succ], apply div_self,
    norm_cast, norm_num [nat.factorial_ne_zero] },
  apply SemiNormedGroup.rescale_map_bound_by,
  have : (p+1+1 : ℝ≥0) = ∑ i : fin (p+1+1), 1,
  { simp only [finset.card_fin, mul_one, finset.sum_const, nsmul_eq_mul, nat.cast_id,
      nat.cast_bit1, nat.cast_add, nat.cast_one] },
  dsimp [system_of_complexes.rescale_functor, double_complex_aux,
    cosimplicial_object.augmented.to_cocomplex_d],
  erw [category.comp_id, if_pos rfl],
  dsimp [cosimplicial_object.coboundary],
  simp only [← nat_trans.app_hom_apply, add_monoid_hom.map_sum, add_monoid_hom.map_gsmul,
    ← homological_complex.hom.f_add_monoid_hom_apply, this],
  apply normed_group_hom.bound_by.sum,
  rintro i -,
  refine (normed_group_hom.bound_by.int_smul _ ((-1) ^ ↑i : ℤ)).le (_ : _ * 1 ≤ 1),
  { apply normed_group_hom.norm_noninc.bound_by_one,
    apply CLC.map_norm_noninc, },
  { simp only [mul_one, int.nat_abs_pow, int.nat_abs_neg, int.nat_abs_one, one_pow, nat.cast_one] },
end

lemma admissible : (col_complex_rescaled r' V Λ M N n).admissible :=
{ d_norm_noninc' :=
  begin
    rintro c i j rfl, cases i,
    { apply d_zero_norm_noninc, },
    { apply d_succ_norm_noninc, }
  end,
  res_norm_noninc :=
  begin
    intros c₁ c₂ i h,
    apply normed_group_hom.bound_by.norm_noninc,
    cases i;
    { apply SemiNormedGroup.rescale_map_bound_by,
      apply normed_group_hom.norm_noninc.bound_by_one,
      apply CLC.map_norm_noninc, },
  end }

end col_complex_rescaled

lemma col_exact'_aux1 [normed_with_aut r V] (c : ℝ≥0ᵒᵖ) (i : ℕ) :
  ∀ x, ∥(((col_complex_rescaled.T_inv_sub_Tinv' r r' V Λ M N (BD.X n) (c_ n)).app c).f i) x∥ ≤
    (1 + r⁻¹) * ∥x∥ :=
begin
  intro x,
  cases i;
  { refine @SemiNormedGroup.rescale_map_bound_by _ _ _ _ _ (1 + r⁻¹) _ x,
    exact CLCFP.T_inv_sub_Tinv_bound_by _ _ _ _ _ _ _ }
end

lemma col_exact'_aux2 [normed_with_aut r V] (c : ℝ≥0ᵒᵖ) (i : ℕ) :
  ∀ y, ∃ x,
    (((col_complex_rescaled.T_inv_sub_Tinv' r r' V Λ M N (BD.X n) (c_ n)).app c).f i) x = y ∧
    ∥x∥ ≤ ↑(r / (1 - r) + 1) * ∥y∥ :=
begin
  haveI : fact (r < 1) := ⟨@lt_trans _ _ r r' 1 (fact.out _) (fact.out _)⟩,
  cases i;
  { refine SemiNormedGroup.rescale_exists_norm_le _ _ _ _,
    intro y,
    obtain ⟨x, h1, h2⟩ := CLCFP.T_inv_sub_Tinv_exists_preimage r r' y 1 zero_lt_one,
    refine ⟨x, h1, _⟩,
    rwa [nnreal.coe_add, nnreal.coe_div, nnreal.coe_sub],
    exact fact.out _ }
end

lemma col_exact' [normed_with_aut r V] [fact (r < 1)]
  (d : ℝ≥0) [pseudo_normed_group.splittable (Λ →+ M) N d]
  (k : ℝ≥0) [fact (1 ≤ k)] (m : ℕ) (c₀ : ℝ≥0) (hdkc₀N : d ≤ (k - 1) * c₀ / N)
  (k' K' : ℝ≥0) [fact (1 ≤ k')] (hk' : k * k ≤ k')
  (hK' : (m + 2 + (r + 1) / (r * (1 - r)) * (m + 2)^2 : ℝ≥0) ≤ K')
  (c₁ c₂ : ℝ≥0) [fact (c₀ ≤ r' * c₁)] [fact (c₀ ≤ c_ n * c₂)] [fact (c₁ ≤ c_ n * c₂)] :
  (double_complex.col'.{u} BD c_ r r' V Λ M N n).is_weak_bounded_exact k' K' m c₂ :=
begin
  have adm := (col_complex_rescaled.admissible.{u} r' V Λ M N (BD.X n)),
  have adm2 := adm.scale_index_left r',
  let T_T := col_complex_rescaled.T_inv_sub_Tinv' r r' V Λ M N (BD.X n) (c_ n),
  have H := (col_complex_rescaled.is_weak_bounded_exact.{u}
    r' V Λ M N (BD.X n) d k (m+1) c₀ hdkc₀N),
  have H1 := H.scale_index_right _ c₂ (c_ n) adm,
  have H2 := (H.scale_index_left _ c₁ r' adm).scale_index_right _ c₂ (c_ n) adm2,
  have key := weak_normed_snake_dual
    (double_complex.col'.{u} BD c_ r r' V Λ M N n) _ _
    (double_complex.col_ι BD c_ r r' V Λ M N n) T_T
    k _ ((m + 1) + 1) _ (1 + r⁻¹) (r / (1 - r) + 1) H1 H2 (adm.scale_index_right _),
  have h_isom : _ := _,
  apply (key _ _ _ h_isom).of_le _ ⟨hk'⟩ _ le_rfl ⟨le_rfl⟩,
  any_goals { clear key adm2 H1 H2 },
  { intros, apply col_exact'_aux1 },
  { intros, apply col_exact'_aux2 },
  { intros c i, apply double_complex.col_ι_range },
  { apply system_of_complexes.admissible_of_isometry (adm.scale_index_right _) h_isom, },
  { refine ⟨le_trans (le_of_eq _) hK'⟩,
    rw [pow_two, ← mul_assoc],
    simp only [nat.cast_add, nat.cast_one, bit0, ← add_assoc, or_false, add_eq_zero_iff,
      one_ne_zero, add_right_inj, mul_eq_mul_right_iff, and_false, div_eq_mul_inv],
    have hr0 : r ≠ 0, { exact ne_of_gt (fact.out _) },
    have h1r : 1 - r ≠ 0,
    { rw [← nnreal.coe_injective.ne_iff, nnreal.coe_sub, nnreal.coe_zero, sub_ne_zero],
      { norm_cast, exact ne_of_gt (fact.out _) },
      { exact fact.out _ } },
    calc (1 + r⁻¹) * (r * (1 - r)⁻¹ + 1)
        = (1 + r⁻¹) * (r * (1 - r)⁻¹ + (1 - r) * (1 - r)⁻¹) : by rw [mul_inv_cancel h1r]
    ... = (1 + r⁻¹) * (1 - r)⁻¹ : congr_arg _ _
    ... = (1 + r⁻¹) * (r * r⁻¹) * (1 - r)⁻¹ : by rw [mul_inv_cancel hr0, mul_one]
    ... = ((1 + r⁻¹) * r) * (r⁻¹ * (1 - r)⁻¹) : by simp only [mul_assoc]
    ... = (r + 1) * (r * (1 - r))⁻¹ : _,
    { rw [← add_mul, add_comm, nnreal.sub_add_cancel_of_le, one_mul], exact fact.out _ },
    { rw [add_mul, one_mul, inv_mul_cancel, mul_inv'],
      exact ne_of_gt (fact.out _) } },
  { intros c i, apply double_complex.col_ι_isometry, }
end

lemma col_exact [normed_with_aut r V] [fact (r < 1)]
  (d : ℝ≥0) [pseudo_normed_group.splittable (Λ →+ M) N d]
  (k : ℝ≥0) [fact (1 ≤ k)] (m : ℕ) (c₀ : ℝ≥0) (hdkc₀N : d ≤ (k - 1) * c₀ / N)
  (k' K' : ℝ≥0) [fact (1 ≤ k')] (hk' : k * k ≤ k')
  (hK' : (m + 2 + (r + 1) / (r * (1 - r)) * (m + 2)^2 : ℝ≥0) ≤ K')
  (c₁ c₂ : ℝ≥0) (_ : fact (c₀ ≤ r' * c₁)) (_ : fact (c₀ ≤ c_ n * c₂)) (_ : fact (c₁ ≤ c_ n * c₂)) :
  ((double_complex.{u} BD c_ r r' V Λ M N).col n).is_weak_bounded_exact k' K' m c₂ :=
begin
  have key := col_exact' BD c_ r r' V Λ M N n d k m c₀ hdkc₀N k' K' hk' hK' c₁ c₂,
  apply key.of_iso (double_complex.col_iso BD c_ r r' V Λ M N n).symm,
  intros,
  apply double_complex.col_iso_inv_strict
end

end thm95
