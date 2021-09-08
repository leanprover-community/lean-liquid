import pseudo_normed_group.FP
import system_of_complexes.basic
import prop819
import pseudo_normed_group.sum_hom

noncomputable theory

open_locale nnreal big_operators
open category_theory opposite simplex_category

local attribute [instance] type_pow

universe variables u u₀ uₘ
-- set_option pp.universes true

namespace system_of_complexes

variables (C : system_of_complexes)

def norm_exact_complex (D : cochain_complex SemiNormedGroup ℕ) : Prop :=
∀ (m : ℕ) (ε : ℝ≥0) (hε : 0 < ε) (x : D.X m) (hx : D.d _ (m+1) x = 0),
  ∃ y : D.X (m-1), D.d _ _ y = x ∧ ∥y∥₊ ≤ (1 + ε) * ∥x∥₊

lemma weak_exact_of_factor_exact (k : ℝ≥0) [fact (1 ≤ k)] (m : ℕ) (c₀ : ℝ≥0)
  (D : ℝ≥0 → cochain_complex SemiNormedGroup ℕ)
  (hD : ∀ c, c₀ ≤ c → norm_exact_complex (D c))
  (f : Π c, C.obj (op $ k * c) ⟶ D c)
  (g : Π c, D c ⟶ C.obj (op c))
  (hf : ∀ c i, ((f c).f i).norm_noninc)
  (hg : ∀ c i, ((g c).f i).norm_noninc)
  (hfg : ∀ c, c₀ ≤ c → f c ≫ g c = C.map (hom_of_le (fact.out _ : c ≤ k * c)).op) :
  C.is_weak_bounded_exact k 1 m c₀ :=
begin
  intros c hc i hi x ε' hε',
  let dx := C.d _ (i+1) x,
  let fx := (f _).f _ x,
  let fdx := (f c).f _ dx,
  let dfx := (D _).d _ (i+1) fx,
  have fdx_dfx : fdx = dfx,
  { simp only [fdx, dfx, fx, ← comp_apply], congr' 1, exact ((f _).comm _ _).symm },
  have hfdx : (D _).d _ (i+2) fdx = 0,
  { calc (D _).d _ (i+2) fdx = (D _).d _ (i+2) ((D _).d _ (i+1) (fx)) : congr_arg _ fdx_dfx
    ... = ((D _).d _ (i+1) ≫ (D _).d _ (i+2)) (fx) : rfl
    ... = 0 : by { rw (D c).d_comp_d _ _ _, refl } },
  let ε : ℝ≥0 := ⟨ε', hε'.le⟩,
  have hε : 0 < ε := hε',
  let δ : ℝ≥0 := ε / (∥dx∥₊ + 1),
  have hδ : 0 < δ,
  { rw [← nnreal.coe_lt_coe],
    exact div_pos hε (lt_of_le_of_lt (nnreal.coe_nonneg _) (lt_add_one _)), },
  obtain ⟨(x' : (D c).X i), (hdx' : (D c).d i (i+1) x' = fdx), hnorm_x'⟩ :=
    (hD _ hc.1) _ δ hδ _ hfdx,
  let gx' := (g _).f _ x',
  have hdfxx' : (D _).d _ (i+1) (fx - x') = 0,
  { rw [normed_group_hom.map_sub, hdx', fdx_dfx], exact sub_self _ },
  obtain ⟨y, hdy, -⟩ := (hD _ hc.1) _ δ hδ _ hdfxx',
  let gy := (g _).f _ y,
  let dgy := C.d _ i gy,
  let gdy := (g _).f _ ((D _).d _ i y),
  have gdy_dgy : gdy = dgy,
  { simp only [gdy, dgy, gy, ← comp_apply], congr' 1, exact ((g _).comm _ _).symm },
  refine ⟨i-1, i+1, rfl, rfl, gy, _⟩,
  simp only [nnreal.coe_one, one_mul],
  have hxdgy : res x - C.d _ _ gy = gx',
  { calc res x - dgy
        = (g _).f _ ((f _).f _ x) - gdy : _
    ... = gx' : by rw [← normed_group_hom.map_sub, hdy, sub_sub_cancel],
    rw [gdy_dgy, ← comp_apply, ← homological_complex.comp_f, hfg _ hc.1], refl },
  rw hxdgy,
  change (∥gx'∥₊ : ℝ) ≤ ∥dx∥₊ + ε,
  simp only [← nnreal.coe_add, nnreal.coe_le_coe],
  calc ∥gx'∥₊
      ≤ ∥x'∥₊ : hg _ _ _
  ... ≤ (1 + δ) * ∥fdx∥₊ : hnorm_x'
  ... ≤ (1 + δ) * ∥dx∥₊ : mul_le_mul' le_rfl (hf _ _ _)
  ... ≤ ∥dx∥₊ + δ * ∥dx∥₊ : by rw [add_mul, one_mul]
  ... ≤ ∥dx∥₊ + ε * 1 : add_le_add le_rfl _
  ... ≤ ∥dx∥₊ + ε : by rw [mul_one],
  dsimp only [δ],
  rw [div_eq_mul_inv, mul_assoc],
  refine mul_le_mul' le_rfl _,
  rw [nnreal.mul_le_iff_le_inv, inv_inv', mul_one],
  { exact (lt_add_one _).le },
  { refine inv_ne_zero (lt_of_le_of_lt _ (lt_add_one _)).ne',
    exact zero_le' }
end

end system_of_complexes

namespace thm95

variables (r' : ℝ) (V : SemiNormedGroup.{u}) (M : Type u) {M₁ M₂ : Type u} (N : ℕ) (d : ℝ≥0)
variables [profinitely_filtered_pseudo_normed_group M] [pseudo_normed_group.splittable M N d]
variables [profinitely_filtered_pseudo_normed_group M₁]
variables [profinitely_filtered_pseudo_normed_group M₂]
variables (f : comphaus_filtered_pseudo_normed_group_hom M₁ M₂) (hf : f.strict)

section open Profinite pseudo_normed_group profinitely_filtered_pseudo_normed_group

@[simps left right]
def FLC_complex_arrow (c : ℝ≥0) : arrow Profinite :=
@arrow.mk _ _ (filtration_obj M₁ c) (filtration_obj M₂ c) $
{ to_fun := pseudo_normed_group.level f hf c,
  continuous_to_fun := f.continuous _ (λ _, rfl) }

end

section open profinitely_filtered_pseudo_normed_group
  comphaus_filtered_pseudo_normed_group

@[simps obj map]
def FLC_complex : system_of_complexes :=
{ obj := λ c, (FLC_functor V).obj (op $ FLC_complex_arrow f hf c.unop),
  map := λ c₁ c₂ h, (FLC_functor V).map $ quiver.hom.op $
    @arrow.hom_mk _ _ (FLC_complex_arrow f hf c₂.unop) (FLC_complex_arrow f hf c₁.unop)
      (⟨_, (@embedding_cast_le _ _ _ _ ⟨le_of_hom h.unop⟩).continuous⟩)
      (⟨_, (@embedding_cast_le _ _ _ _ ⟨le_of_hom h.unop⟩).continuous⟩)
      (by { ext, refl }),
  map_id' := λ c,
  begin
    convert (FLC_functor V).map_id _,
    simp only [unop_id, ←op_id, quiver.hom.op_inj.eq_iff, nat_trans.id_app],
    ext; refl,
  end,
  map_comp' := λ c₁ c₂ c₃ h1 h2,
  begin
    convert (FLC_functor V).map_comp _ _,
    simp only [← op_comp, quiver.hom.op_inj.eq_iff, nat_trans.comp_app],
    ext; refl,
  end, }
.

end

namespace FLC_complex
open pseudo_normed_group

variables (c₁ c₂ : ℝ≥0) [fact (c₁ ≤ c₂)]

def aux_space (c₁ c₂ : ℝ≥0) [fact (c₁ ≤ c₂)] :=
{ p : filtration M₂ c₁ × filtration M₁ c₂ // cast_le p.1 = level f hf c₂ p.2 }

namespace aux_space
open profinitely_filtered_pseudo_normed_group comphaus_filtered_pseudo_normed_group

instance : topological_space (aux_space f hf c₁ c₂) :=
by { delta aux_space, apply_instance }

instance : t2_space (aux_space f hf c₁ c₂) :=
by { delta aux_space, apply_instance }

instance : totally_disconnected_space (aux_space f hf c₁ c₂) :=
subtype.totally_disconnected_space

instance : compact_space (aux_space f hf c₁ c₂) :=
{ compact_univ :=
  begin
    rw embedding_subtype_coe.is_compact_iff_is_compact_image,
    simp only [set.image_univ, subtype.range_coe_subtype],
    refine is_closed.is_compact _,
    refine is_closed_eq
      ((embedding_cast_le _ _).continuous.comp continuous_fst)
      ((f.continuous _ _).comp continuous_snd),
    intro, refl
  end }

end aux_space

def AuxSpace : Profinite := Profinite.of (aux_space f hf c₁ c₂)

namespace AuxSpace

open profinitely_filtered_pseudo_normed_group

@[simps] def ι : filtration_obj M₁ c₁ ⟶ AuxSpace f hf c₁ c₂ :=
{ to_fun := λ x, ⟨⟨level f hf c₁ x, Filtration.cast_le M₁ c₁ c₂ x⟩, rfl⟩,
  continuous_to_fun :=
  begin
    apply continuous_induced_rng,
    refine continuous.prod_mk (f.continuous _ (λ _, rfl)) (Filtration.cast_le M₁ c₁ c₂).continuous,
  end }

@[simps] def fst : AuxSpace f hf c₁ c₂ ⟶ filtration_obj M₂ c₁ :=
{ to_fun := _,
  continuous_to_fun := continuous_fst.comp continuous_subtype_coe }

@[simps] def snd : AuxSpace f hf c₁ c₂ ⟶ filtration_obj M₁ c₂ :=
{ to_fun := _,
  continuous_to_fun := continuous_snd.comp continuous_subtype_coe }

@[simps left right]
def fstₐ : arrow Profinite := arrow.mk (fst f hf c₁ c₂)

include d

lemma fst_surjective [fact (0 < N)] (h : c₁ / N + d ≤ c₂ * N⁻¹) :
  function.surjective (fst _ (sum_hom_strict M N) c₁ c₂) :=
begin
  intros y,
  dsimp at y,
  obtain ⟨x, hx1, hx2⟩ := exists_sum N d _ _ y.2,
  simp only [fst_to_fun, function.comp_app],
  refine ⟨⟨⟨y, ⟨x, _⟩⟩, _⟩, rfl⟩,
  { erw rescale.mem_filtration, refine filtration_mono h hx2 },
  { simp only [pseudo_normed_group.level, sum_hom_apply, subtype.coe_mk, ← hx1], refl },
end

end AuxSpace

open AuxSpace profinitely_filtered_pseudo_normed_group

@[simps]
def sum_hom₀ [fact (0 < N)] (c : ℝ≥0) : filtration_obj (rescale N (M^N)) c ⟶ filtration_obj M c :=
⟨pseudo_normed_group.level (sum_hom M N) (sum_hom_strict M N) c,
  (sum_hom M N).continuous _ (λ _, rfl)⟩

@[simps left right hom]
def sum_homₐ [fact (0 < N)] (c : ℝ≥0) : arrow Profinite := arrow.mk (sum_hom₀ M N c)

def sum_homₐ_fstₐ [fact (0 < N)] : sum_homₐ M N c₁ ⟶ fstₐ _ (sum_hom_strict M N) c₁ c₂ :=
{ left := AuxSpace.ι _ _ _ _,
  right := 𝟙 _, }

def fstₐ_sum_homₐ [fact (0 < N)] : fstₐ _ (sum_hom_strict M N) c₁ c₂ ⟶ sum_homₐ M N c₂ :=
{ left := snd _ _ _ _,
  right := Filtration.cast_le _ _ _,
  w' := by { ext1 ⟨x, h⟩, exact h.symm } }

include d

lemma weak_bounded_exact (k : ℝ≥0) [hk : fact (1 ≤ k)] (m : ℕ) (c₀ : ℝ≥0) [fact (0 < N)]
  (hdkc₀N : d ≤ (k - 1) * c₀ / N) :
  (FLC_complex V _ (sum_hom_strict M N)).is_weak_bounded_exact k 1 m c₀ :=
begin
  let D := λ c, (FLC_functor V).obj (op $ fstₐ _ (sum_hom_strict M N) c (k * c)),
  let f := λ c, (FLC_functor V).map (fstₐ_sum_homₐ M N c (k * c)).op,
  let g := λ c, (FLC_functor V).map (sum_homₐ_fstₐ M N c (k * c)).op,
  refine system_of_complexes.weak_exact_of_factor_exact _ k m c₀ D _ f g _ _ _,
  { intros c hc,
    suffices : function.surjective ((unop (op (fstₐ (sum_hom M N) _ c (k * c)))).hom),
    { intros i ε hε x hx, cases i,
      { simp only [nat.one_ne_zero, homological_complex.shape, complex_shape.up_rel,
          exists_and_distrib_left, not_false_iff, normed_group_hom.zero_apply],
        refine ⟨(prop819_degree_zero _ this _ x hx).symm, 0, _⟩,
        simp only [nnnorm_zero, zero_le'] },
      exact prop819 _ this _ ε hε x hx },
    refine fst_surjective M N d c (k * c) _,
    calc c / N + d
        ≤ c / N + (k - 1) * c₀ / N : add_le_add le_rfl hdkc₀N
    ... ≤ c / N + (k - 1) * c / N : add_le_add le_rfl _
    ... ≤ 1 * c / N + (k - 1) * c / N : by rw one_mul
    ... = k * c / N : _,
    { simp only [div_eq_mul_inv],
      refine mul_le_mul' (mul_le_mul' le_rfl hc) le_rfl, },
    { simp only [div_eq_mul_inv, mul_assoc],
      rw ← add_mul, congr,
      rw [← nnreal.eq_iff, nnreal.coe_add, nnreal.coe_sub hk.1, add_sub_cancel'_right], } },
  { intros c i, exact FLC_functor_map_norm_noninc _ _ _ },
  { intros c i, exact FLC_functor_map_norm_noninc _ _ _ },
  { intros c hc,
    dsimp only [f, g, FLC_complex_map],
    rw [← category_theory.functor.map_comp, ← op_comp],
    refl }
end

end FLC_complex


end thm95
