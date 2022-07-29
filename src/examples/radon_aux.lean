import challenge
import topology.algebra.module.weak_dual
import topology.sets.closeds


noncomputable theory

local attribute [instance]
  locally_constant.seminormed_add_comm_group
  locally_constant.pseudo_metric_space

open_locale nnreal big_operators

-- move me
lemma ite_mem {α : Type*} (s : set α) (p : Prop) {_ : decidable p} (x y : α) :
  ((if p then x else y) ∈ s) ↔ ((p ∧ x ∈ s) ∨ (¬p ∧ y ∈ s)) :=
begin
  split_ifs with h,
  { simp only [h, true_and, not_true, false_and, or_false] },
  { simp only [h, false_and, not_false_iff, true_and, false_or] }
end

namespace topological_space
namespace clopens

variables {X Y : Type*} [topological_space X] [topological_space Y] [has_zero Y]

def indicator_continuous (U : clopens X) (f : X → Y) (hf : continuous f) :
  continuous (set.indicator (U : set X) f) :=
begin
  constructor, intros V hV,
  set W : set X := (U : set X).indicator f ⁻¹' V,
  by_cases h0 : (0:Y) ∈ V,
  { suffices : W = f ⁻¹' V ∪ Uᶜ,
    { rw this, exact (hV.preimage hf).union U.clopen.compl.is_open },
    classical, ext x,
    simp only [set.mem_preimage, set.mem_union_eq, set.mem_compl_eq, set_like.mem_coe,
      set.indicator_apply],
    split_ifs with hxU,
    { simp only [hxU, not_true, or_false] },
    { simp only [h0, hxU, true_iff, not_false_iff, or_true], }, },
  { suffices : W = f ⁻¹' V ∩ U,
    { rw this, exact (hV.preimage hf).inter U.clopen.is_open },
    classical, ext x,
    simp only [set.mem_preimage, set.mem_union_eq, set.mem_compl_eq, set_like.mem_coe,
      set.indicator_apply],
    split_ifs with hxU,
    { simp only [hxU, set.mem_inter_eq, set.mem_preimage, set_like.mem_coe, and_true] },
    { simp only [h0, false_iff, set.mem_inter_eq, set.mem_preimage, set_like.mem_coe, not_and],
      intro, assumption, } }
end

-- generalize
@[simps]
def indicator (U : clopens X) : C(X,ℝ) :=
⟨set.indicator (U : set X) 1, U.indicator_continuous _ $ @continuous_const _ _ _ _ 1⟩

instance [discrete_topology X] : has_singleton X (clopens X) :=
{ singleton := λ x, ⟨{x}, is_clopen_discrete _⟩ }

@[simp] lemma mem_singleton_iff [discrete_topology X] (x y : X) :
  x ∈ ({y} : clopens X) ↔ x = y :=
set.mem_singleton_iff

def discrete_finpartition [discrete_topology X] [fintype X] : finpartition (⊤ : clopens X) :=
{ parts := finset.univ.map ⟨λ x : X, {x}, λ x y, by simp only [set_like.ext_iff, mem_singleton_iff, eq_iff_eq_cancel_left, imp_self]⟩,
  sup_indep := begin
    sorry
  end,
  sup_parts := begin
    rw [eq_top_iff],
    rintro x -,
    simp only [finset.sup_map, function.embedding.coe_fn_mk, function.comp.left_id],
    sorry
  end,
  not_bot_mem := begin
    simp only [finset.mem_map, finset.mem_univ, function.embedding.coe_fn_mk, exists_true_left, not_exists, set_like.ext_iff, mem_singleton_iff, not_forall],
    intro x, use x,
    simp only [eq_self_iff_true, true_iff],
    exact not_false
  end }

end clopens
end topological_space

section

variables (X : Profinite.{0})

-- The abstract completion package exhibiting `C(X,ℝ)` as the completion of `LC(X,ℝ)`.
example : abstract_completion (locally_constant X ℝ) := locally_constant.pkg X ℝ

example : (locally_constant.pkg X ℝ).space = C(X,ℝ) := rfl
example : (locally_constant.pkg X ℝ).coe = locally_constant.to_continuous_map := rfl

example (f : locally_constant X ℝ →L[ℝ] ℝ) : uniform_continuous f :=
begin
  apply uniform_continuous_of_tendsto_zero,
  simpa using f.continuous.tendsto 0,
end

abbreviation signed_Radon_measure := weak_dual ℝ C(X,ℝ)

def lc_to_c : locally_constant X ℝ →L[ℝ] C(X,ℝ) :=
{ to_fun := locally_constant.to_continuous_map,
  map_add' := λ f g, rfl,
  map_smul' := λ a f, rfl,
  cont := (locally_constant.pkg X ℝ).continuous_coe } -- ;-)

def signed_Radon_measure.comparison :
  signed_Radon_measure X →L[ℝ] weak_dual ℝ (locally_constant X ℝ) :=
{ to_fun := λ f, f.comp (lc_to_c _),
  map_add' := λ f g, rfl,
  map_smul' := λ a f, rfl,
  cont := begin
    apply weak_dual.continuous_of_continuous_eval,
    intro f,
    apply weak_dual.eval_continuous (lc_to_c X f),
  end }

local attribute [instance] abstract_completion.uniform_struct

-- generalize this to arbitrary abstract completions:
lemma dense_range_coe₂ :
  dense_range (λ p : locally_constant X ℝ × locally_constant X ℝ, (lc_to_c X p.1, lc_to_c X p.2)) :=
(locally_constant.pkg X ℝ).dense.prod_map (locally_constant.pkg X ℝ).dense

/-

def signed_Radon_measure.inverse :
  C(weak_dual ℝ (locally_constant X ℝ), signed_Radon_measure X) :=
{ to_fun := λ f,
  { to_fun := (locally_constant.pkg X ℝ).extend f,
    map_add' := by admit; begin
      letI : add_group (locally_constant.pkg X ℝ).space :=
        continuous_map.add_group,
      letI : topological_add_group (locally_constant.pkg X ℝ).space :=
        continuous_map.topological_add_group,
      rw ← prod.forall',
      refine is_closed_property (dense_range_coe₂ X) _ _,
      { apply is_closed_eq,
        { refine (locally_constant.pkg X ℝ).continuous_extend.comp continuous_add },
        { refine continuous.add _ _;
          refine (locally_constant.pkg X ℝ).continuous_extend.comp _,
          exact continuous_fst,
          exact continuous_snd } },
      { rintro ⟨φ, ψ⟩, dsimp only,
        have hf := continuous_linear_map.uniform_continuous f,
        rw [← (lc_to_c X).map_add],
        erw [(locally_constant.pkg X ℝ).extend_coe hf, (locally_constant.pkg X ℝ).extend_coe hf,
          (locally_constant.pkg X ℝ).extend_coe hf, map_add], }
    end,
    map_smul' := by admit; begin
      letI : add_group (locally_constant.pkg X ℝ).space :=
        continuous_map.add_group,
      letI : topological_add_group (locally_constant.pkg X ℝ).space :=
        continuous_map.topological_add_group,
      letI : has_smul ℝ (locally_constant.pkg X ℝ).space :=
        continuous_map.has_smul,
      letI : has_continuous_smul ℝ (locally_constant.pkg X ℝ).space :=
        continuous_map.has_continuous_smul,
      intros r φ,
      apply (locally_constant.pkg X ℝ).induction_on φ; clear φ,
      { apply is_closed_eq,
        { refine (locally_constant.pkg X ℝ).continuous_extend.comp
            (continuous_const.smul continuous_id), },
        { refine continuous_const.smul (locally_constant.pkg X ℝ).continuous_extend } },
      { intro φ,
        have hf := continuous_linear_map.uniform_continuous f,
        erw [← (lc_to_c X).map_smul, (locally_constant.pkg X ℝ).extend_coe hf,
          (locally_constant.pkg X ℝ).extend_coe hf, map_smul],
        refl }
    end,
    cont := (locally_constant.pkg X ℝ).continuous_extend },
  continuous_to_fun := begin
    apply weak_dual.continuous_of_continuous_eval,
    intro f,
    dsimp,
    admit
    -- apply (locally_constant.pkg X ℝ).induction_on f; clear f,
    -- { admit, },
    -- { admit }
  end }

def signed_Radon_measure.equiv :
   signed_Radon_measure X ≃L[ℝ] weak_dual ℝ (locally_constant X ℝ) :=
{ inv_fun := signed_Radon_measure.inverse _,
  left_inv := begin
    intro μ, ext1 f,
    change (locally_constant.pkg X ℝ).extend (μ ∘ (lc_to_c X)) f = μ f,
    apply (locally_constant.pkg X ℝ).induction_on f; clear f,
    { apply is_closed_eq,
      { exact (locally_constant.pkg X ℝ).continuous_extend },
      { exact continuous_linear_map.continuous μ } },
    { intro f,
      have aux : uniform_continuous (μ ∘ (lc_to_c X)) :=
        (continuous_linear_map.uniform_continuous μ).comp (lc_to_c X).uniform_continuous,
      rw [(locally_constant.pkg X ℝ).extend_coe aux],
      refl }
  end,
  right_inv := begin
    intro μ, ext1 f,
    show (locally_constant.pkg X ℝ).extend μ (lc_to_c X f) = μ f,
    have hμ := continuous_linear_map.uniform_continuous μ,
    erw [(locally_constant.pkg X ℝ).extend_coe hμ],
  end,
  continuous_to_fun := (signed_Radon_measure.comparison X).cont,
  continuous_inv_fun := (signed_Radon_measure.inverse X).continuous,
  ..(signed_Radon_measure.comparison X) }

-/

variables {X}
open topological_space (clopens)

def signed_Radon_measure.pnorm_rel_partition (p : ℝ≥0)
  (𝓤 : finpartition (⊤ : clopens X)) (μ : signed_Radon_measure X) :=
∑ U in 𝓤.parts, ∥μ U.indicator∥₊^(p:ℝ)

def signed_Radon_measure.is_p_bdd (μ : signed_Radon_measure X) (p : ℝ≥0) (c : ℝ≥0) : Prop :=
∀ 𝓤 : finpartition (⊤ : clopens X), μ.pnorm_rel_partition p 𝓤 ≤ c

end

section bdd

open topological_space (clopens)

variables (p : ℝ≥0) (c : ℝ≥0) (X : Profinite.{0})

def signed_Radon_p_measure_bdd (p : ℝ≥0) (c : ℝ≥0) (X : Profinite.{0}) :=
{μ : signed_Radon_measure X | μ.is_p_bdd p c }

def signed_Radon_measure_equiv_of_Fintype (X : Fintype.{0}) :
  signed_Radon_measure (Fintype.to_Profinite.obj X) ≃ real_measures p X :=
{ to_fun := λ μ x, μ (topological_space.clopens.indicator {x}),
  inv_fun := λ μ,
  { to_fun := λ f, ∑ x : X, μ x * f x,
    map_add' := λ f g,
      by simp only [continuous_map.coe_add, pi.add_apply, mul_add, finset.sum_add_distrib],
    map_smul' := λ r f,
      by simp only [continuous_map.coe_smul, pi.smul_apply, mul_smul_comm, finset.smul_sum, ring_hom.id_apply],
    cont := begin
      apply continuous_finset_sum,
      rintro i -,
      refine continuous_const.mul (continuous_map.continuous_eval_const i)
    end },
  left_inv := λ μ, begin
    ext f,
    change ∑ (x : X), μ (topological_space.clopens.indicator {x}) * f x = μ f,
    suffices : f = ∑ x : X, f x • (topological_space.clopens.indicator {x}),
    { conv_rhs { rw [this, map_sum] },
      refine finset.sum_congr rfl _,
      rintro x -,
      rw [map_smul, smul_eq_mul, mul_comm], },
    ext x,
    simp only [continuous_map.coe_sum, continuous_map.coe_smul, fintype.sum_apply, pi.smul_apply, algebra.id.smul_eq_mul],
    rw finset.sum_eq_single_of_mem, swap 4, { exact x }, swap 2, { exact finset.mem_univ _ }, swap,
    { rintro y - hy,
      simp only [hy.symm, topological_space.clopens.indicator_apply, set.indicator_of_not_mem,
        set_like.mem_coe, topological_space.clopens.mem_singleton_iff, not_false_iff, mul_zero], },
    { simp only [topological_space.clopens.indicator_apply, set.indicator_of_mem, set_like.mem_coe,
        topological_space.clopens.mem_singleton_iff, pi.one_apply, mul_one], }
  end,
  right_inv := λ μ, begin
    ext x,
    change ∑ (y : ↥X), μ y * _ = μ x,
    rw finset.sum_eq_single_of_mem, swap 4, { exact x }, swap 2, { exact finset.mem_univ _ }, swap,
    { rintro y - hy,
      simp only [hy, topological_space.clopens.indicator_apply, set.indicator_of_not_mem,
        set_like.mem_coe, topological_space.clopens.mem_singleton_iff, not_false_iff, mul_zero], },
    { simp only [topological_space.clopens.indicator_apply, set.indicator_of_mem, set_like.mem_coe,
        topological_space.clopens.mem_singleton_iff, pi.one_apply, mul_one], }
  end }

lemma signed_Radon_measure_pnorm_le [fact (0 < p)] [fact (p ≤ 1)] (X : Fintype.{0})
  (𝓤 : finpartition (⊤ : clopens (Fintype.to_Profinite.obj X)))
  (μ : signed_Radon_measure (Fintype.to_Profinite.obj X)) :
  μ.pnorm_rel_partition p 𝓤 ≤ μ.pnorm_rel_partition p
    (@topological_space.clopens.discrete_finpartition _ _ _ X.2) :=
begin
  set X' := Fintype.to_Profinite.obj X, classical,
  have : ∀ U : clopens X',
    ∥μ U.indicator∥₊^(p:ℝ) ≤ ∑ x in (finset.univ : finset X).filter (λ x, x ∈ U),
      ∥μ (topological_space.clopens.indicator {x})∥₊^(p:ℝ),
  sorry { intro U,
    have h0p : 0 < p := fact.out _,
    have hp1 : p ≤ 1 := fact.out _,
    refine le_trans _ (nnreal.rpow_sum_le_sum_rpow _ _ h0p hp1),
    refine nnreal.rpow_le_rpow _ h0p.le,
    refine le_trans (le_of_eq _) (nnnorm_sum_le _ _),
    rw [← map_sum],
    congr' 2,
    ext x,
    simp only [topological_space.clopens.indicator_apply, continuous_map.coe_sum, finset.sum_apply],
    rw [set.indicator_apply],
    split_ifs with hxU,
    { rw finset.sum_eq_single_of_mem, swap 4, { exact x },
      { simp only [set.indicator_apply, set_like.mem_coe,
          topological_space.clopens.mem_singleton_iff, eq_self_iff_true, if_true], },
      { simp only [finset.mem_filter, finset.mem_univ, true_and], exact hxU },
      { rintro y - hy,
        simp only [hy.symm, set.indicator_of_not_mem, set_like.mem_coe,
          topological_space.clopens.mem_singleton_iff, not_false_iff] } },
    { rw finset.sum_eq_zero,
      rintro y hy,
      simp only [finset.mem_filter, finset.mem_univ, true_and] at hy,
      simp only [set.indicator_apply, set_like.mem_coe, topological_space.clopens.mem_singleton_iff,
         pi.one_apply, ite_eq_right_iff, one_ne_zero],
      rintro rfl, exact hxU hy } },
  refine le_trans (finset.sum_le_sum $ λ U hU, this U) (le_of_eq _),
  rw finset.sum_sigma',
  apply finset.sum_bij,
  swap 5, { intros a ha, exact {a.2} },
  { intros,
    simp only [topological_space.clopens.discrete_finpartition, finset.mem_map, finset.mem_univ,
      function.embedding.coe_fn_mk, exists_true_left, exists_apply_eq_apply], },
  { intros x hx, refl },
  { rintro ⟨U,x⟩ ⟨V,y⟩ hx hy h,
    simp only [finset.mem_sigma, finset.mem_filter, finset.mem_univ, true_and,
      set_like.ext_iff] at hx hy h ⊢,
    specialize h x,
    simp only [topological_space.clopens.mem_singleton_iff, eq_self_iff_true, true_iff] at h,
    subst y,
    simp only [heq_iff_eq, eq_self_iff_true, and_true],
    sorry },
  { intros U hU,
    simp only [topological_space.clopens.discrete_finpartition, finset.mem_map, finset.mem_univ,
      function.embedding.coe_fn_mk, exists_true_left] at hU,
    obtain ⟨x, rfl⟩ := hU,
    sorry }
end

lemma signed_Radon_measure_pnorm_eq (X : Fintype.{0})
  (μ : signed_Radon_measure (Fintype.to_Profinite.obj X)) :
  μ.pnorm_rel_partition p (@topological_space.clopens.discrete_finpartition _ _ _ X.2) =
  ∑ (s : ↥X), ∥(signed_Radon_measure_equiv_of_Fintype p X) μ s∥₊ ^ (p:ℝ) :=
begin
  symmetry,
  apply finset.sum_bij,
  swap 5, { intros x hx, exact {x} },
  { intros x hx,
    simp only [topological_space.clopens.discrete_finpartition, finset.mem_map, finset.mem_univ,
      function.embedding.coe_fn_mk, exists_true_left, exists_apply_eq_apply], },
  { intros x hx, refl },
  { rintro x y hx hy h, rw set_like.ext_iff at h, specialize h x,
    simpa only [topological_space.clopens.mem_singleton_iff, eq_self_iff_true, true_iff] using h, },
  { intros U hU,
    simp only [topological_space.clopens.discrete_finpartition, finset.mem_map, finset.mem_univ,
      function.embedding.coe_fn_mk, exists_true_left] at hU,
    obtain ⟨x, rfl⟩ := hU,
    refine ⟨x, finset.mem_univ _, rfl⟩, }
end

lemma signed_Radon_p_measure_bdd_iff [fact (0 < p)] [fact (p ≤ 1)]
  (X : Fintype.{0}) (μ : signed_Radon_measure (Fintype.to_Profinite.obj X)) :
  μ.is_p_bdd p c ↔
  signed_Radon_measure_equiv_of_Fintype p X μ ∈ pseudo_normed_group.filtration (real_measures p X) c :=
begin
  rw [real_measures.mem_filtration_iff, real_measures.nnnorm_def],
  simp only [signed_Radon_measure.is_p_bdd, ← signed_Radon_measure_pnorm_eq],
  split,
  { intro h, apply h, },
  { intros h 𝓤, apply (signed_Radon_measure_pnorm_le _ _ _ _).trans h },
end

def signed_Radon_p_measure_bdd_equiv (X : Fintype.{0}) [fact (0 < p)] [fact (p ≤ 1)] :
  signed_Radon_p_measure_bdd p c (Fintype.to_Profinite.obj X) ≃
  pseudo_normed_group.filtration (real_measures p X) c :=
{ to_fun := λ μ, ⟨signed_Radon_measure_equiv_of_Fintype p X μ, begin
    rw ← signed_Radon_p_measure_bdd_iff, exact μ.2
  end⟩,
  inv_fun := λ μ, ⟨(signed_Radon_measure_equiv_of_Fintype p X).symm μ, begin
    dsimp [signed_Radon_p_measure_bdd],
    rw signed_Radon_p_measure_bdd_iff, simpa only [equiv.apply_symm_apply] using μ.2
  end⟩,
  left_inv := λ μ, subtype.ext $ (signed_Radon_measure_equiv_of_Fintype p X).symm_apply_apply _,
  right_inv := λ μ, subtype.ext $ (signed_Radon_measure_equiv_of_Fintype p X).apply_symm_apply _ }

lemma continuous_signed_Radon_p_measure_bdd_equiv_symm
  (X : Fintype.{0}) [fact (0 < p)] [fact (p ≤ 1)] :
  continuous (signed_Radon_p_measure_bdd_equiv p c X).symm :=
begin
  apply continuous_subtype_mk,
  apply weak_dual.continuous_of_continuous_eval, intros t,
  dsimp [signed_Radon_measure_equiv_of_Fintype],
  let e : X → (pseudo_normed_group.filtration (real_measures p X) c) → ℝ :=
    λ x μ, (μ : real_measures p X) x * t x,
  suffices : ∀ x, continuous (e x),
  { apply continuous_finset_sum, rintros x -, exact this x },
  intros x,
  let e' : (pseudo_normed_group.filtration (real_measures p X) c) → ℝ :=
    λ μ, (μ : real_measures p X) x,
  have he : e x = t x • e',
  { ext, dsimp, rw mul_comm, },
  rw he, refine continuous.smul (continuous_const : continuous (λ _, t x)) (_ : continuous e'),
  dsimp [e'],
  change continuous ((λ μ : X → ℝ, μ x) ∘
    (λ μ : (pseudo_normed_group.filtration (real_measures p X) c), (μ : real_measures p X))),
  refine continuous.comp (continuous_apply x) _,
  exact continuous_subtype_coe,
end

instance t2_space_signed_Radon_measure (X : Profinite.{0}) :
  t2_space (signed_Radon_measure X) :=
let e : signed_Radon_measure X → C(X,ℝ) → ℝ := λ μ, μ in
t2_space.mk $ λ x y h,
  @separated_by_continuous _ _ _ (Pi.topological_space)
  begin
    convert Pi.t2_space,
    intros t,
    exact t3_space.t2_space ℝ,
  end e continuous_induced_dom _ _ (λ c, h $ continuous_linear_map.ext $ λ f, congr_fun c f)

instance t2_space_signed_Radon_p_measure_bdd (X : Fintype.{0}) :
  t2_space (signed_Radon_p_measure_bdd p c (Fintype.to_Profinite.obj X)) :=
subtype.t2_space

def signed_Radon_p_measure_bdd_homeo (X : Fintype.{0}) [fact (0 < p)] [fact (p ≤ 1)] :
  signed_Radon_p_measure_bdd p c (Fintype.to_Profinite.obj X) ≃ₜ
  pseudo_normed_group.filtration (real_measures p X) c :=
{ continuous_to_fun := begin
    rw continuous_iff_is_closed, intros S hS,
    dsimp [-Fintype.to_Profinite_obj],
    erw ← (signed_Radon_p_measure_bdd_equiv _ _ _).symm.image_eq_preimage,
    apply is_compact.is_closed,
    apply hS.is_compact.image,
    apply continuous_signed_Radon_p_measure_bdd_equiv_symm,
  end,
  continuous_inv_fun := continuous_signed_Radon_p_measure_bdd_equiv_symm _ _ _,
  ..(signed_Radon_p_measure_bdd_equiv _ _ _) }

end bdd
