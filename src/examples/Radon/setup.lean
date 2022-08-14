import topology.category.Profinite.as_limit
import topology.continuous_function.algebra
import locally_constant.SemiNormedGroup
import locally_constant.completion
import analysis.special_functions.pow
import topology.algebra.module.weak_dual
import analysis.mean_inequalities_pow
import real_measures.condensed

open_locale nnreal big_operators classical

noncomputable theory

open category_theory
open category_theory.limits
open topological_space

local attribute [instance]
  locally_constant.seminormed_add_comm_group
  locally_constant.pseudo_metric_space

lemma real.pow_nnnorm_sum_le
  {ι : Type*} (S : finset ι) (r : ι → ℝ)
  (p : ℝ≥0) [fact (0 < p)] [fact (p ≤ 1)] :
  ∥ ∑ i in S, r i ∥₊^(p : ℝ) ≤ ∑ i in S, ∥ r i ∥₊^(p : ℝ) :=
begin
  refine finset.le_sum_of_subadditive (λ x : ℝ, ∥ x ∥₊^(p : ℝ)) _ _
    S r,
  { simp only [nnnorm_zero, nnreal.rpow_eq_zero_iff, eq_self_iff_true, ne.def,
      nnreal.coe_eq_zero, true_and],
    exact ne_of_gt (fact.out _) },
  { intros x y,
    dsimp,
    refine le_trans _ (nnreal.rpow_add_le_add_rpow _ _ _ _),
    rw nnreal.rpow_le_rpow_iff,
    apply nnnorm_add_le,
    any_goals { exact_mod_cast fact.out _ },
    any_goals { assumption } }
end

namespace locally_constant

instance normed_space (X : Type*)
  [topological_space X] [compact_space X] :
  normed_space ℝ (locally_constant X ℝ) :=
{ norm_smul_le := λ a f, by simpa only [norm_def, coe_smul, pi.smul_apply, algebra.id.smul_eq_mul,
    real.norm_eq_abs, abs_mul, mul_comm (abs a)] using
      (real.supr_mul_of_nonneg (abs_nonneg _) _).symm.le,
  ..(infer_instance : module ℝ _) }

lemma nnnorm_apply_le_nnnorm (X : Type*)
  [topological_space X] [compact_space X]
  (e : locally_constant X ℝ) (x : X) :
  ∥ e x ∥₊ ≤ ∥ e ∥₊ :=
begin
  change _ ≤ Sup _,
  apply le_cSup,
  let S := _, change bdd_above S, suffices : is_compact S, apply is_compact.bdd_above this,
  apply is_compact_range, refine continuous.comp _ e.continuous, exact continuous_norm,
  use x, refl,
end

/--  The evaluation map at a point of a topological space, bundled as a linear map from
locally constant functions to the real numbers. -/
def linear_eval (X : Type*)
  [topological_space X] (x : X) :
  locally_constant X ℝ →ₗ[ℝ] ℝ :=
{ to_fun := λ e, e x,
  map_add' := λ f g, rfl,
  map_smul' := λ r f, rfl }


lemma continuous_eval (X : Type*)
  [topological_space X] [compact_space X] (x : X) :
  continuous (λ e : locally_constant X ℝ, e x) :=
begin
  change continuous (linear_eval X x),
  let E := linear_map.mk_continuous_of_exists_bound (linear_eval X x) _,
  swap,
  use 1, intros e, rw one_mul, apply nnnorm_apply_le_nnnorm,
  exact E.continuous
end

end locally_constant

namespace topological_space.clopens

lemma indicator_continuous {X Y : Type*} [topological_space X] [topological_space Y] [has_zero Y]
  (U : clopens X) (f : X → Y) (hf : continuous f) :
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

/--  The indicator function on clopen sets are continuous functions. -/
def indicator {X : Type*} [topological_space X] (U : clopens X) :
  C(X,ℝ) :=
{ to_fun := set.indicator U 1,
  continuous_to_fun := indicator_continuous _ _ continuous_one }

lemma indicator_one_inverse_image {X : Type*} (U : set X) (s : set ℝ) :
  (U.indicator 1 ⁻¹' s) = set.univ ∨ (U.indicator 1 ⁻¹' s) = U ∨
  (U.indicator 1 ⁻¹' s) = Uᶜ ∨ (U.indicator 1 ⁻¹' s) = ∅ :=
begin
  by_cases s1 : (1 : ℝ) ∈ s;
  by_cases s0 : (0 : ℝ) ∈ s,
  work_on_goal 1 { refine or.inl _},
  work_on_goal 2 { refine or.inr (or.inl _) },
  work_on_goal 3 { refine or.inr (or.inr (or.inl _)) },
  work_on_goal 4 { refine or.inr (or.inr (or.inr _)) },
  all_goals
  { ext x,
    by_cases xU : x ∈ U,
    { simp only [xU, s1, set.mem_preimage, set.indicator_of_mem, pi.one_apply, set.mem_compl_eq,
        not_true, set.mem_univ, set.mem_empty_eq] },
    { simp only [xU, s0, set.mem_preimage, set.indicator_of_not_mem, not_false_iff,
      set.mem_compl_eq, set.mem_univ, set.mem_empty_eq] } }
end

/--  The indicator function of a clopen set, bundled as a locally constant function. -/
def indicator_LC {X : Type*} [topological_space X] (U : clopens X) :
  locally_constant X ℝ :=
{ to_fun := set.indicator U 1,
  is_locally_constant := λ s, begin
    rcases indicator_one_inverse_image ↑U s with h | h | h | h;
    rw h,
    exacts [is_open_univ, U.clopen.is_open, (Uᶜ).clopen.is_open, is_open_empty]
  end }

lemma indicator_apply {X : Type*} [topological_space X] (U : clopens X) (x) :
  U.indicator x = if x ∈ U then 1 else 0 := rfl

lemma indicator_LC_apply {X : Type*} [topological_space X] (U : clopens X) (x) :
  U.indicator_LC x = if x ∈ U then 1 else 0 := rfl

end topological_space.clopens

namespace discrete_quotient

/--  Given a discrete topological space `T` that is a quotient of a topological space `X`, and
an element `t : T`, `fiber T t` is the clopen subset of `X` that is the inverse image of `t` under
the quotient map `X → T`. -/
def fibre {X : Type*} [topological_space X] (T : discrete_quotient X)
  (t : T) : clopens X :=
{ carrier := T.proj ⁻¹' {t},
  clopen' := fiber_clopen T {t} }

/--  When the topological space `X` is discrete, `equiv_bot` is the equivalence between `X` and the
bottom element of the discrete quotients of `X`.  In other words, the identity map from `X` to
itself *is*  a discrete quotient and `equiv_bot` is this bijection. -/
def equiv_bot {X : Type*} [topological_space X] [discrete_topology X] :
  X ≃ (⊥ : discrete_quotient X) :=
equiv.of_bijective (discrete_quotient.proj _)
⟨λ x y h, quotient.exact' h, discrete_quotient.proj_surjective _⟩

lemma mem_fibre_iff {X : Type*} [topological_space X]
  (T : discrete_quotient X) (a : T) (b : X) :
  T.proj b ∈ discrete_quotient.fibre _ (equiv_bot a) ↔
  b ∈ discrete_quotient.fibre T a :=
begin
  obtain ⟨a,rfl⟩ := discrete_quotient.proj_surjective _ a,
  dsimp [fibre, equiv_bot],
  let TT : discrete_quotient T := ⊥,
  change T.proj b ∈ equiv_bot ⁻¹' {equiv_bot (T.proj a)} ↔ T.proj b ∈ {T.proj a},
  simp,
end

lemma mem_fibre_iff' {X : Type*} [topological_space X]
  (T : discrete_quotient X) (a : (⊥ : discrete_quotient T)) (b : X) :
  T.proj b ∈ discrete_quotient.fibre _ a ↔
  b ∈ discrete_quotient.fibre T (equiv_bot.symm a) :=
begin
  rw [← equiv_bot.apply_symm_apply a, mem_fibre_iff],
  simp,
end

/--  Given a continuous (`hf`), surjective (`hf'`) function `f : X → Y` between topological spaces
`X` and `Y`, and a discrete quotient `T` of `Y`, `comap_equiv f hf hf' T` is the bijection between
between the  comap of `T` along `f` and `T` itself.
-/
def comap_equiv {X Y : Type*} [topological_space X] [topological_space Y]
  (f : X → Y) (hf : continuous f) (hf' : function.surjective f)
  (T : discrete_quotient Y) :
  T.comap hf ≃ T :=
equiv.of_bijective (discrete_quotient.map $ le_refl _)
begin
  split,
  { rintros ⟨x⟩ ⟨y⟩ h,
    apply quotient.sound',
    apply quotient.exact' h },
  { rintros ⟨x⟩,
    obtain ⟨x,rfl⟩ := hf' x,
    use discrete_quotient.proj _ x, refl }
end

lemma comap_mem_fibre_iff {X Y : Type*} [topological_space X] [topological_space Y]
  (f : X → Y) (hf : continuous f)
  (T : discrete_quotient Y) (a : T.comap hf) (b : X) :
  b ∈ discrete_quotient.fibre (T.comap hf) a ↔
  f b ∈ discrete_quotient.fibre T (discrete_quotient.map (le_refl _) a) :=
begin
  dsimp [fibre],
  change b ∈ (T.comap hf).proj ⁻¹' {a} ↔
    f b ∈ T.proj ⁻¹' {_},
  obtain ⟨a,rfl⟩ := discrete_quotient.proj_surjective _ a,
  simp only [set.mem_preimage, set.mem_singleton_iff, map_proj_apply],
  split,
  { intros h, apply quotient.sound', apply quotient.exact' h, },
  { intros h, apply quotient.sound', apply quotient.exact' h, },
end

end discrete_quotient

lemma locally_constant.sum_apply {ι X Y : Type*} [topological_space X] [add_comm_monoid Y]
  (f : ι → locally_constant X Y) (S : finset ι) (t : X) :
  (∑ i in S, f i) t = ∑ i in S, (f i t) :=
begin
  let ee : locally_constant X Y →+ X → Y := locally_constant.coe_fn_add_monoid_hom,
  change (ee (∑ i in S, f i)) t = ∑ i in S, (ee (f i) t),
  rw [ee.map_sum, finset.sum_apply],
end

lemma locally_constant.eq_sum {X : Type*} [topological_space X] [compact_space X]
  (e : locally_constant X ℝ) :
  e = ∑ t : e.discrete_quotient,
    e.locally_constant_lift t • (e.discrete_quotient.fibre t).indicator_LC :=
begin
  ext t,
  simp_rw [locally_constant.sum_apply, locally_constant.smul_apply],
  suffices :
    ∑ (x : ↥(e.discrete_quotient)),
      (e.locally_constant_lift) x • ((e.discrete_quotient.fibre x).indicator_LC) t =
    ∑ x in { e.discrete_quotient.proj t },
      (e.locally_constant_lift) x • ((e.discrete_quotient.fibre x).indicator_LC) t,
  { rw this,
    simp only [algebra.id.smul_eq_mul, finset.sum_singleton],
    change _ = e t * _, symmetry, convert mul_one _,
    rw [topological_space.clopens.indicator_LC_apply, if_pos],
    change e.discrete_quotient.proj t ∈ _, simp, -- clopens is missing some `mem_mk` lemma...
  },
  symmetry,
  apply finset.sum_subset, simp only [finset.subset_univ],
  intros s _ ht,
  convert smul_zero _,
  rw [topological_space.clopens.indicator_LC_apply, if_neg],
  contrapose! ht,
  change e.discrete_quotient.proj t ∈ _ at ht,
  simp only [finset.mem_singleton, set.mem_singleton_iff] at ht ⊢,
  exact ht.symm,
end

/--  Given a point `x : X` is a discrete topological space `X`,
`topological_space.clopens.singleton x` is the point `x`, bundled as a clopen subset of `X`. -/
def topological_space.clopens.singleton {X : Type*}
  [topological_space X] [discrete_topology X] (x : X) :
  clopens X :=
{ carrier := {x},
  clopen' := by tidy }

lemma locally_constant.eq_sum_of_fintype {X : Type*} [fintype X]
  [topological_space X] [discrete_topology X]
  (e : locally_constant X ℝ) :
  e =
  ∑ t : X, e t • (topological_space.clopens.singleton t).indicator_LC :=
begin
  ext t,
  rw locally_constant.sum_apply,
  rw finset.sum_eq_single t,
  { change _ = _ • ite _ _ _,
    rw [if_pos, smul_eq_mul], erw mul_one,
    change _ = _, refl },
  { intros x _ hx,
    change _ • ite _ _ _ = _,
    rw [if_neg, smul_zero], change _ ≠ _, exact hx.symm },
  { intros h, exfalso, apply h, exact finset.mem_univ _ }
end

/--  Given a continuous function `f : X → Y` between topological spaces `X` and `Y`,
`continuous_map.comap f` is the `ℝ`-linear pre-composition with `f` as a function from
the `ℝ`-valued continuous functions on `Y` to the `ℝ`-valued continuous functions on `X`. -/
def continuous_map.comap {X Y : Type*} [topological_space X] [topological_space Y]
  (f : C(X,Y)) : C(Y,ℝ) →L[ℝ] C(X,ℝ) :=
{ to_fun := λ g, g.comp f,
  map_add' := λ _ _, rfl,
  map_smul' := λ _ _, rfl,
  cont := by refine continuous_map.continuous_comp_left f }

/--  Given a continuous function `f : X → Y` between topological spaces `X` and `Y`,
`continuous_map.comap_LC_linear_map f` is the `ℝ`-linear pre-composition with `f` as a function from
the locally constant `ℝ`-valued continuous functions on `Y` to the locally constant `ℝ`-valued
continuous functions on `X`.

`continuous_map.comap_LC` is similar, except that it also bundles continuity of the resulting
function among spaces of continuous maps. -/
def continuous_map.comap_LC_linear_map {X Y : Type*} [topological_space X] [topological_space Y]
  (f : C(X,Y)) : locally_constant Y ℝ →ₗ[ℝ] locally_constant X ℝ :=
{ to_fun := λ g,
  { to_fun := g ∘ f,
    is_locally_constant := λ S,
      by { rw set.preimage_comp, apply is_open.preimage f.2, apply g.2, } },
  map_add' := λ _ _, rfl,
  map_smul' := λ _ _, rfl }

/--  Given a continuous function `f : X → Y` between topological spaces `X` and `Y`,
`continuous_map.comap_LC_linear_map f` is the `ℝ`-linear pre-composition with `f` as a *continuous*
function from the locally constant `ℝ`-valued continuous functions on `Y` to the locally constant
`ℝ`-valued continuous functions on `X`.

`continuous_map.comap_LC_linear_map` is similar, but does not bundle continuity of the resulting
function among spaces of continuous maps. -/
def continuous_map.comap_LC {X Y : Type*} [topological_space X] [compact_space X]
  [topological_space Y] [compact_space Y]
  (f : C(X,Y)) : locally_constant Y ℝ →L[ℝ] locally_constant X ℝ :=
{ cont := begin
    apply (f.comap_LC_linear_map.mk_continuous_of_exists_bound _).continuous,
    use 1, intros e, rw one_mul,
    by_cases (is_empty X),
    { have : (f.comap_LC_linear_map) e = 0, ext x, exact h.elim x, rw this,
      simp },
    change Sup _ ≤ _,
    apply cSup_le,
    simp only [not_is_empty_iff] at h, obtain ⟨x⟩ := h,
    use ∥ e (f x) ∥, use x, refl,
    rintros b ⟨x,rfl⟩, dsimp,
    exact_mod_cast locally_constant.nnnorm_apply_le_nnnorm _ e (f x),
  end,
  ..(continuous_map.comap_LC_linear_map f) }

/--  Given a compact topological space `X`, the inclusion of locally constant functions on `X` into
the space of all continuous functions is a continuous `ℝ`-linear map. -/
def lc_to_c (X : Type*) [topological_space X] [compact_space X] :
  locally_constant X ℝ →L[ℝ] C(X,ℝ) :=
{ to_fun := λ f, f.to_continuous_map,
  map_add' := λ _ _, rfl,
  map_smul' := λ _ _, rfl,
  cont := begin
    apply isometry.continuous,
    intros f g,
    simp only [edist_dist, dist_eq_norm, continuous_map.norm_eq_supr_norm,
      locally_constant.norm_def, locally_constant.to_continuous_map_eq_coe,
      continuous_map.coe_sub, locally_constant.coe_continuous_map, pi.sub_apply],
    refl,
  end }

namespace weak_dual

/--  Given topological `ℝ`-vector spaces `A` and `B` and a continuous, `ℝ`-linear map `f : A → B`
between them, `comap f` is the pre-composition with `f` as a continuous, `ℝ`-linear map between
the weak `ℝ`-linear dual of `B` to the weak `ℝ`-linear dual of `A`. -/
def comap {A B : Type*}
  [add_comm_group A] [module ℝ A] [topological_space A]
  [add_comm_group B] [module ℝ B] [topological_space B]
  (f : A →L[ℝ] B) :
  weak_dual ℝ B →L[ℝ] weak_dual ℝ A :=
{ to_fun := λ g, g.comp f,
  map_add' := λ _ _, rfl,
  map_smul' := λ _ _, rfl,
  cont := begin
    apply weak_dual.continuous_of_continuous_eval,
    intros a,
    apply weak_dual.eval_continuous,
  end }

/--  Given a compact topological space `X`, an element `μ` in the weak, `ℝ`-linear dual of the
continuous functions on `X`, and two non-negative real numbers `p` and `c`, `bdd μ p c` is the
statement that the sum of the `p`-th powers of the absolute values of the measures of all the
clopen subsets of `X` is bounded above by `c`.

See the actual definition for what "all the clopen subsets" really means!

`bdd_LC` is similar, but uses the dual of locally constant functions.  -/
def bdd {X : Type*} [topological_space X] [compact_space X]
  (μ : weak_dual ℝ C(X,ℝ)) (p c : ℝ≥0) : Prop :=
∀ (T : discrete_quotient X),
  ∑ t : T, ∥ μ (T.fibre t).indicator ∥₊^(p : ℝ) ≤ c

/--  Given a compact topological space `X`, an element `μ` in the weak, `ℝ`-linear dual of the
locally constant functions on `X`, and two non-negative real numbers `p` and `c`, `bdd μ p c` is the
statement that the sum of the `p`-th powers of the absolute values of the measures of all the
clopen subsets of `X` is bounded above by `c`.

See the actual definition for what "all the clopen subsets" really means!

`bdd` is similar, but uses the dual of continuous functions.  -/
def bdd_LC {X : Type*} [topological_space X] [compact_space X]
  (μ : weak_dual ℝ (locally_constant X ℝ)) (p c : ℝ≥0) : Prop :=
∀ (T : discrete_quotient X),
  ∑ t : T, ∥ μ (T.fibre t).indicator_LC ∥₊^(p : ℝ) ≤ c

lemma bdd_LC_comap {X Y : Type*} {p c : ℝ≥0} [fact (0 < p)]
  [topological_space X] [compact_space X]
  [topological_space Y] [compact_space Y]
  (μ : weak_dual ℝ (locally_constant X ℝ)) (hμ : μ.bdd_LC p c) (f : C(X,Y)) :
  (weak_dual.comap f.comap_LC μ).bdd_LC p c :=
begin
  intros T,
  convert hμ (T.comap f.2) using 1,
  let ι : T.comap f.2 → T := discrete_quotient.map (le_refl _),
  have hι : function.injective ι,
  { rintros ⟨⟩ ⟨⟩ h,
    apply quotient.sound',
    apply quotient.exact' h },
  let S₁ := _, change S₁ = _,
  have : S₁ = ∑ t in finset.univ.image ι,
    ∥ ((comap f.comap_LC) μ) (T.fibre t).indicator_LC ∥₊ ^ (p : ℝ),
  { symmetry, apply finset.sum_subset, simp,
    intros x _ hx,
    --simp only [finset.mem_image, finset.mem_univ, exists_true_left, not_exists] at hx,
    suffices : ((comap f.comap_LC) μ) (T.fibre x).indicator_LC = 0,
    { simp only [this, nnnorm_zero, nnreal.rpow_eq_zero_iff, eq_self_iff_true,
        ne.def, nnreal.coe_eq_zero, true_and],
      exact ne_of_gt (fact.out (0 < p)) },
    dsimp [comap], convert μ.map_zero,
    ext t,
    dsimp [continuous_map.comap_LC, topological_space.clopens.indicator_LC_apply],
    apply if_neg,
    contrapose! hx,
    rw finset.mem_image,
    refine ⟨discrete_quotient.proj _ t, finset.mem_univ _, hx⟩ },
  rw this, clear this, symmetry,
  fapply finset.sum_bij,
  { intros a _, exact ι a },
  { intros, dsimp, erw finset.mem_image, refine ⟨a, finset.mem_univ _, rfl⟩ },
  { intros a ha, congr' 2,
    dsimp [comap], congr' 1,
    ext t,
    erw topological_space.clopens.indicator_LC_apply,
    erw topological_space.clopens.indicator_LC_apply,
    rw discrete_quotient.comap_mem_fibre_iff },
  { intros a₁ a₂ h₁ h₂ hh, apply hι, exact hh },
  { rintros b hb,
    rw finset.mem_image at hb,
    obtain ⟨b,hh,hb⟩ := hb,
    use [b,hh,hb.symm] },
end

lemma bdd_comap {X Y : Type*} {p c : ℝ≥0} [fact (0 < p)]
  [topological_space X] [compact_space X]
  [topological_space Y] [compact_space Y]
  (μ : weak_dual ℝ C(X,ℝ)) (hμ : μ.bdd p c) (f : C(X,Y)) :
  (weak_dual.comap f.comap μ).bdd p c :=
λ t, by apply bdd_LC_comap (comap (lc_to_c X) μ) hμ f t

end weak_dual
