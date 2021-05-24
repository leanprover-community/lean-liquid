import prop_92.prop_92
import normed_snake_dual
import combinatorial_lemma
import thm95.constants
import thm95.double_complex
import thm95.col_exact_prep

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

section
open PolyhedralLattice

def CLCFP' : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ ⥤ ℝ≥0ᵒᵖ ⥤ SemiNormedGroup :=
(ProFiltPseuNormGrpWithTinv.Pow r' n ⋙ (_root_.Filtration r').flip).op ⋙
  functor.op_hom _ _ ⋙ (whiskering_right ℝ≥0ᵒᵖ Profiniteᵒᵖ _).obj (CLC V)

def Cech_nerve' : cosimplicial_object.augmented (ℝ≥0ᵒᵖ ⥤ SemiNormedGroup) :=
(cosimplicial_object.augmented.whiskering_obj.{u} _ _ (CLCFP' r' V n)).obj
  (Cech_nerve r' Λ M N)

@[simps X d]
def col_complex_aux : cochain_complex (ℝ≥0ᵒᵖ ⥤ SemiNormedGroup) ℕ :=
(Cech_nerve' r' V Λ M N n).to_cocomplex
.

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

@[simps obj map]
def col_complex : system_of_complexes :=
(col_complex_aux r' V Λ M N n).as_functor
.

def aug_map :=
((ProFiltPseuNormGrpWithTinv.Pow r' n).map (Cech_augmentation_map r' Λ M N))
  .to_profinitely_filtered_pseudo_normed_group_hom

section open profinitely_filtered_pseudo_normed_group_with_Tinv_hom
lemma aug_map_strict : (aug_map r' Λ M N n).strict :=
to_profinitely_filtered_pseudo_normed_group_hom_strict _
end

lemma col_complex_iso₁ :
  col_complex r' V Λ M N n ≅ FLC_complex V _ (aug_map_strict r' Λ M N n) :=
sorry


lemma col_complex_iso₁_strict (c : ℝ≥0ᵒᵖ) (i : ℕ) :
  isometry (((col_complex_iso₁ r' V Λ M N n).hom.app c).f i) :=
sorry

lemma col_complex_iso₃ :
  FLC_complex V _ (profinitely_filtered_pseudo_normed_group.sum_hom_strict ((↥Λ →+ ↥M)^n) N) ≅
  col_complex r' V Λ M N n :=
sorry

lemma col_complex_iso₃_strict (c : ℝ≥0ᵒᵖ) (i : ℕ) :
  isometry (((col_complex_iso₃ r' V Λ M N n).hom.app c).f i) :=
sorry

lemma col_complex.is_weak_bounded_exact (d : ℝ≥0) [pseudo_normed_group.splittable ((Λ →+ M)^n) N d]
  (k : ℝ≥0) [fact (1 ≤ k)] (m : ℕ) (c₀ : ℝ≥0) (hdkc₀N : d ≤ (k - 1) * c₀ / N) :
  (col_complex r' V Λ M N n).is_weak_bounded_exact k 1 m c₀ :=
begin
  have key := FLC_complex.weak_bounded_exact V ((Λ →+ M)^n) N d k m c₀ hdkc₀N,
  exact key.of_iso _ (λ c, col_complex_iso₃_strict r' V Λ M N n (op c)),
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

def T_inv_sub_Tinv_f_succ_succ [normed_with_aut r V] (c : ℝ≥0ᵒᵖ) (i : ℕ) :
  ((col_complex_rescaled.{u} r' V Λ M N n).obj c).X (i + 1) ⟶
    (((col_complex_rescaled.{u} r' V Λ M N n).scale_index_left r').obj c).X (i + 1) :=
(SemiNormedGroup.rescale (i+1)!).map $ (CLCFP.T_inv_sub_Tinv r r' V _ _ n).app _

def T_inv_sub_Tinv_f [normed_with_aut r V] (c : ℝ≥0ᵒᵖ) :
  Π i, ((col_complex_rescaled.{u} r' V Λ M N n).obj c).X i ⟶
  (((col_complex_rescaled.{u} r' V Λ M N n).scale_index_left r').obj c).X i
| 0     := (SemiNormedGroup.rescale 0!).map $ (CLCFP.T_inv_sub_Tinv r r' V _ _ n).app _
| (i+1) := T_inv_sub_Tinv_f_succ_succ r r' V Λ M N n c i

lemma T_inv_sub_Tinv_comm [normed_with_aut r V] (c : ℝ≥0ᵒᵖ) :
  ∀ i, T_inv_sub_Tinv_f r r' V Λ M N n c i ≫
    (((col_complex_rescaled r' V Λ M N n).scale_index_left r').obj c).d i (i+1) =
  ((col_complex_rescaled r' V Λ M N n).obj c).d i (i+1) ≫
    T_inv_sub_Tinv_f r r' V Λ M N n c (i+1)
| 0     := sorry -- by { ext, dsimp [T_inv_sub_Tinv_f, system_of_complexes.scale_index_left, nnreal.MulLeft], sorry }
| (i+1) := sorry

def T_inv_sub_Tinv [normed_with_aut r V] :
  col_complex_rescaled r' V Λ M N n ⟶ (col_complex_rescaled r' V Λ M N n).scale_index_left r' :=
{ app := λ c,
  { f := T_inv_sub_Tinv_f r r' V Λ M N n c,
    comm' := by { rintros i j (rfl : i + 1 = j), exact T_inv_sub_Tinv_comm r r' V Λ M N n c i } },
  naturality' := sorry }

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

section open homological_complex system_of_complexes

lemma col_ι_f_comm [normed_with_aut r V] (c : ℝ≥0ᵒᵖ) :
  ∀ i, col_ι_f BD c_ r r' V Λ M N n c i ≫
    (((col_complex_rescaled r' V Λ M N (BD.X n)).scale_index_right (c_ n)).obj c).d i (i + 1) =
  ((col' BD c_ r r' V Λ M N n).obj c).d i (i + 1) ≫ col_ι_f BD c_ r r' V Λ M N n c (i + 1)
| 0     :=
begin
  dsimp only [col_ι_f, col_ι_f_succ, col'_obj, functor.map_homological_complex_obj_d,
    modify_d, eval_map, scale_index_right, ScaleIndexRight_obj_obj, col_complex_rescaled_obj,
    scale'_app],
  sorry
  -- rw [← (SemiNormedGroup.scale ↑0! ↑(0 + 1)!).naturality],
  -- refine SemiNormedGroup.scale_comm 0! 1! _ _ _ _ _,
  -- rw [dif_pos rfl],
  -- rw [category.assoc], -- dif_pos rfl], -- ← nat_trans.naturality],
end
| (i+1) := sorry

end

lemma col_ι [normed_with_aut r V] :
  col'.{u} BD c_ r r' V Λ M N n ⟶
    (col_complex_rescaled.{u} r' V Λ M N (BD.X n)).scale_index_right (c_ n) :=
{ app := λ c,
  { f := col_ι_f BD c_ r r' V Λ M N n c,
    comm' := by { rintro i j (rfl : i + 1 = j), apply col_ι_f_comm } },
  naturality' :=
  begin
    sorry
  end }

end double_complex

namespace col_complex_rescaled

lemma admissible : (col_complex_rescaled r' V Λ M N n).admissible := sorry

end col_complex_rescaled

open universal_constants (hiding N)

lemma col_exact' [normed_with_aut r V] [fact (r < 1)]
  (d : ℝ≥0) [pseudo_normed_group.splittable (Λ →+ M) N d]
  (k : ℝ≥0) [fact (1 ≤ k)] (m : ℕ) (c₀ : ℝ≥0) (hdkc₀N : d ≤ (k - 1) * c₀ / N)
  (k' K' : ℝ≥0) [fact (1 ≤ k')] (hk' : k * k ≤ k')
  (hK' : (m + 2 + ((r + 1) / r) * (r / (1 - r) + 1) * (m + 2) * (m + 2) : ℝ≥0) ≤ K')
  (c₁ c₂ : ℝ≥0) [fact (c₀ ≤ r' * c₁)] [fact (c₀ ≤ c_ n * c₂)] [fact (c₁ ≤ c_ n * c₂)] :
  (double_complex.col'.{u} BD c_ r r' V Λ M N n).is_weak_bounded_exact k' K' m c₂ :=
begin
  have adm := (col_complex_rescaled.admissible.{u} r' V Λ M N (BD.X n)),
  have adm2 := adm.scale_index_left r',
  let T_T := (system_of_complexes.ScaleIndexRight (c_ n)).map
    (col_complex_rescaled.T_inv_sub_Tinv r r' V Λ M N (BD.X n)),
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
  { sorry },
  { sorry },
  { sorry },
  { apply system_of_complexes.admissible_of_isometry (adm.scale_index_right _) h_isom, },
  { refine ⟨le_trans (le_of_eq _) hK'⟩,
    simp only [nat.cast_add, nat.cast_one, bit0, ← add_assoc, or_false, add_eq_zero_iff,
      one_ne_zero, add_right_inj, mul_eq_mul_right_iff, and_false, div_eq_mul_inv],
    rw [add_mul, one_mul, mul_inv_cancel],
    exact ne_of_gt (fact.out _) },
  { intros c i,
    apply normed_group_hom.isometry_of_norm,
    intro v,
    sorry }
end

lemma col_exact [normed_with_aut r V] [fact (r < 1)]
  (d : ℝ≥0) [pseudo_normed_group.splittable (Λ →+ M) N d]
  (k : ℝ≥0) [fact (1 ≤ k)] (m : ℕ) (c₀ : ℝ≥0) (hdkc₀N : d ≤ (k - 1) * c₀ / N)
  (k' K' : ℝ≥0) [fact (1 ≤ k')] (hk' : k * k ≤ k')
  (hK' : (m + 2 + ((r + 1) / r) * (r / (1 - r) + 1) * (m + 2) * (m + 2) : ℝ≥0) ≤ K')
  (c₁ c₂ : ℝ≥0) (_ : fact (c₀ ≤ r' * c₁)) (_ : fact (c₀ ≤ c_ n * c₂)) (_ : fact (c₁ ≤ c_ n * c₂)) :
  ((double_complex.{u} BD c_ r r' V Λ M N).col n).is_weak_bounded_exact k' K' m c₂ :=
begin
  have key := col_exact' BD c_ r r' V Λ M N n d k m c₀ hdkc₀N k' K' hk' hK' c₁ c₂,
  apply key.of_iso (double_complex.col_iso BD c_ r r' V Λ M N n).symm,
  intros,
  apply double_complex.col_iso_inv_strict
end

end thm95
