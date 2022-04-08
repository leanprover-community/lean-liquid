import linear_algebra.dimension
import ring_theory.principal_ideal_domain
import set_theory.ordinal
import set_theory.ordinal_arithmetic
import linear_algebra.free_module.basic

open_locale big_operators


section finset

universes u v w
variables {β : Type u} {α : Type v} {α' : Type w}  [comm_monoid β]

@[simp, to_additive]
lemma finset.prod_comap (s : finset α') (e : α → α') (f : α' → β)
  (he : set.inj_on e (e ⁻¹' ↑s))
  (hs : (s : set α') ⊆ set.range e):
  (∏ x in (s.preimage e he), f (e x)) = ∏ x in s, f x :=
begin
  haveI : Π (x : α'), decidable (x ∈ set.range e) := λ x, classical.prop_decidable _,
  haveI := classical.type_decidable_eq α',
  have hs : s = finset.image e (s.preimage e he),
  { rw finset.image_preimage,
    ext,
    split,
    { intro ha,
      simp only [finset.mem_filter, set.mem_range],
      refine ⟨ha, _⟩,
      exact_mod_cast set.mem_of_subset_of_mem hs ha
    },
    { simp only [finset.mem_filter, set.mem_range, and_imp, forall_exists_index],
      exact (λ H _ _, H)
    }
  },
  have hpre : e ⁻¹' ↑s = s.preimage e he := by rw finset.coe_preimage,
  have : ∏ x in (finset.image e (s.preimage e he)), f x = ∏ x in (s.preimage e he), f (e x),
  apply finset.prod_image,
  intros x hx y hy h,
  have hx : x ∈ e ⁻¹' ↑s := by rw hpre; exact hx,
  have hy : y ∈ e ⁻¹' ↑s := by rw hpre; exact hy,
  exact he hx hy h,
  rw ←this,
  rw ←hs
end

end finset

section finsupp

variables {α : Type*} {M : Type*} {R : Type*}
variables [semiring R] [add_comm_monoid M] [module R M]

variables {α' : Type*}

lemma finsupp.total_comap_domain'
  (v : α' → M) (f : α → α') (l : α' →₀ R) (hf : set.inj_on f (f ⁻¹' ↑l.support))
  (hsupp : (l.support : set α') ⊆ set.range f) :
(finsupp.total α M R (v ∘ f)) (finsupp.comap_domain f l hf) = ∑ (i : α') in l.support, l i • v i :=
begin
  haveI := classical.type_decidable_eq α',
  rw finsupp.total_apply,
  simp [finsupp.sum, finsupp.comap_domain],
  exact finset.sum_comap l.support f (λ x, l x • v x) hf hsupp
end

end finsupp


open submodule.is_principal set submodule

universe u

-- Equivalent of lt_of_lt_of_le for unbundled orders. (??)
lemma lt_of_lt_of_le_unbundled {α : Type u} {r : α → α → Prop} [is_strict_total_order' α r] {a b c : α}
  (hab : r a b) (hbc : ¬r c b) :
r a c :=
begin
  have t : r b c ∨ b = c ∨ r c b := trichotomous b c,
  cases t,
  exact is_trans.trans a b c hab t,
  cases t,
  rw ←t,
  exact hab,
  exact false.elim (hbc t)
end

-- Characterization of le for unbundled orders. (??)
lemma le_unbundled {α : Type u} {r : α → α → Prop} [is_strict_total_order' α r] {a b : α} :
  r a b ∨ a = b ↔  ¬r b a :=
begin
  split,
  intro h,
  cases h,
  by_contradiction h',
  exact irrefl a (is_trans.trans _ _ _ h h'),
  rw h,
  exact irrefl b,
  intro h,
  have t : r a b ∨ a = b ∨ r b a := trichotomous a b,
  cases t,
  exact or.intro_left _ t,
  cases t,
  exact or.intro_right _ t,
  exact false.elim (h t)
end

variables {R : Type*} [comm_ring R]
variables {M : Type*} [add_comm_group M] [module R M]

section aux_lemmas

variables {o : ordinal} {a : {i // i < o} → R}

lemma support_remove
  {i : ordinal}
  {j_good : { i // a i ≠ 0}}
  (hj: j_good.1.1.succ = i)
  {l l': {i // a i ≠ 0} →₀ R}
  (hsupp: ((l.support) : set { i // a i ≠ 0}) ⊆ λ (x : {i // a i ≠ 0}), x.1.1 < i)
  (hl' : l' = l + finsupp.single j_good (-(l j_good))) :
(l'.support : set { i // a i ≠ 0}) ⊆ (λ x : { i // a i ≠ 0}, x.1.1 < j_good.1.1) :=
begin
  let good := { i  // a i ≠ 0},
  have hl'j : l' j_good = 0,
  { simp only [hl', finsupp.coe_add, pi.add_apply, finsupp.single_eq_same, add_right_neg] },
  intros x hx,
  have hx₁ : x ∈ l'.support := hx,
  have hl' : ∀ x : good, x ≠ j_good → l' x = l x,
  intros x hx,
  simp only [hl', finsupp.single_eq_of_ne hx.symm, finsupp.coe_add, pi.add_apply, add_zero],
  by_contradiction,
  have h : ¬ x.1.1 < j_good.1.1 := h,
  have h := eq_or_lt_of_le (not_lt.1 h),
  cases h,
  { have h_1 : j_good = x := by simp at h_1; ext; exact h_1,
    rw ←h_1 at hx₁,
    rw l'.3 j_good at hx₁,
    contradiction
  },
  { have h_1' : j_good.1.1 ≠ x.1.1 := ne_of_lt h_1,
    have h_1' : j_good ≠ x,  -- todo: can't ext do this?
    simp at h_1',
    rw ne.def,
    apply mt subtype.ext_iff.1,
    apply mt subtype.ext_iff.1,
    exact h_1',
    have : l'.to_fun x = l x := hl' x h_1'.symm,
    have hx' := hx₁,
    rw l'.3 x at hx',
    rw this at hx',
    have hxi : j_good.1.1.succ ≤ x.1.1 := succ_order.succ_le_of_lt h_1,
    rw hj at hxi,
    have := not_mem_subset hsupp (not_lt_of_ge hxi),
    have := mt (l.3 x).2 this,
    contradiction
  }
end

-- Auxiliary lemma for proving linear independence at limit ordinals.
lemma lin_ind_limit
  {BB : { i // a i ≠ 0} → M}
  {i : ordinal}
  (hio : i ≤ o)
  (hlim : ordinal.is_limit i)
  (H : ∀ (k : ordinal), k < i → k ≤ o → ∀ (l : { i // a i ≠ 0} →₀ R),
      ((l.support : set { i // a i ≠ 0}) ⊆ λ (x : { i // a i ≠ 0}), x.1.1 < k) →
      finsupp.total { i // a i ≠ 0} M R BB l = 0 → l = 0)
  {l : { i // a i ≠ 0} →₀ R}
  (hsupp : (l.support : set {i // a i ≠ 0}) ⊆ (λ x : { i // a i ≠ 0}, x.1.1 < i))
  (hl : finsupp.total { i // a i ≠ 0} M R BB l = 0) :
l = 0 :=
begin
  let good := {i  // a i ≠ 0},
  by_cases hemp : l.support.nonempty,
  { let m := l.support.max' hemp,
    dsimp at hsupp,
    have hm₀ : ↑↑m < i := by exact_mod_cast mem_of_subset_of_mem hsupp (finset.max'_mem l.support hemp),
    have hm : m.1.1.succ < i := (ordinal.succ_lt_of_is_limit hlim).2 hm₀,
    have hmo : m.1.1.succ ≤ o := le_of_lt (lt_of_lt_of_le hm hio),
    have hsub : (l.support : set good) ⊆ (λ x : good, x.1.1 < m.1.1.succ),
    intros x hx,
    have hx : x ∈ l.support := hx,
    have : x.1.1 ≤ m.1.1 := finset.le_max' l.support x hx,
    exact order.lt_succ_iff.2 this,
    exact H m.1.1.succ hm hmo l hsub hl
  },
  { rw finset.not_nonempty_iff_eq_empty at hemp,
    exact finsupp.support_eq_empty.1 hemp
  }
end


-- Auxiliary lemma for proving the span property at limit ordinals.
lemma span_limit
  {N : submodule R M}
  {BB : { i // a i ≠ 0} → M}
  {i : ordinal}
  (hio : i ≤ o)
  (hlim : ordinal.is_limit i)
  {B : basis {i // i < o} R M}
  (H : ∀ (k : ordinal), k < i → k ≤ o → ∀ (l : {i // i < o} →₀ R),
      (l.support : set {i // i < o}) ⊆ (λ x, x.1 < k) →
      finsupp.total { i // i < o} M R B l ∈ N →
      finsupp.total { i // i < o} M R B l ∈ submodule.span R (range BB))
  {l : { i // i < o} →₀ R}
  (hsupp : (l.support : set {i // i < o}) ⊆ (λ x, x.1 < i))
  (hl : finsupp.total { i // i < o} M R B l ∈ N) :
finsupp.total { i // i < o} M R B l ∈ submodule.span R (range BB) :=
begin
  let ords := {i  // i < o},
  by_cases hemp : l.support.nonempty,
  { let m := l.support.max' hemp,
    dsimp at hsupp,
    have hm₀ : ↑m < i := by exact_mod_cast mem_of_subset_of_mem hsupp (finset.max'_mem l.support hemp),
    have hm : m.1.succ < i := (ordinal.succ_lt_of_is_limit hlim).2 hm₀,
    have hmo : m.1.succ ≤ o := le_of_lt (lt_of_lt_of_le hm hio),
    have hsub : (l.support : set ords) ⊆ (λ x : ords, x.1 < m.1.succ),
    intros x hx,
    have hx : x ∈ l.support := hx,
    have : x.1 ≤ m.1 := finset.le_max' l.support x hx,
    exact order.lt_succ_iff.2 this,
    exact H m.1.succ hm hmo l hsub hl
  },
  { rw finset.not_nonempty_iff_eq_empty at hemp,
    simp only [finsupp.support_eq_empty.1 hemp, _root_.map_zero, zero_mem]
  }
end

-- Auxiliary lemma for proving linear independence at successor ordinals.
lemma lin_ind_succ
  [is_domain R]
  {N : submodule R M}
  {B : basis {i // i < o} R M}
  {BB : { i  // a i ≠ 0} → N}
  (hB_BB : ∀ i : ordinal, ∀ l : {i // a i ≠ 0} →₀ R,
      ((l.support : set {i // a i ≠ 0}) ⊆ λ x, x.1.1 < i) →
      ∃ lB : {i // i < o} →₀ R, ((lB.support : set {i // i < o}) ⊆ λ x, x.1 < i) ∧
        finsupp.total {i // i < o} M R B lB = finsupp.total {i // a i ≠ 0} N R BB l)
  (hcoordB : ∀ i : { i // a i ≠ 0}, (B.coord i) (BB i) ≠ 0)
  {i : ordinal}
  (hio : i ≤ o)
  (hlim : ¬ordinal.is_limit i)
  (H : ∀ (k : ordinal), k < i → k ≤ o → ∀ (l : { i // a i ≠ 0} →₀ R),
      ((l.support : set { i // a i ≠ 0}) ⊆ λ (x : { i  // a i ≠ 0}), x.1.1 < k) →
      finsupp.total { i  // a i ≠ 0} N R BB l = 0 → l = 0)
  {l : { i // a i ≠ 0} →₀ R}
  (hsupp : (l.support : set {i  // a i ≠ 0}) ⊆ (λ x : { i // a i ≠ 0}, x.1.1 < i))
  (hl : finsupp.total { i  // a i ≠ 0} N R BB l = 0) :
l = 0 :=
begin
  let ords := { i // i < o},
  let good := { i  // a i ≠ 0},
  dsimp at hsupp,
  dsimp only [ordinal.is_limit] at hlim,
  repeat {push_neg at hlim},
  by_cases hi : i ≠ 0,
  rcases (hlim hi) with ⟨j, hj⟩,
  have hji : j < i := hj.1,
  have hjo : j < o := lt_of_lt_of_le hji hio,
  have hj : j.succ = i := le_antisymm (ordinal.succ_le.2 hj.1) hj.2,

  have not_j_lt_x : ∀ (x : good), ∀ (j : ordinal), x ∈ l.support → j < x.1.1 → j.succ = i → false,
  { intros x j hx h_1 hj,
    have hi : j.succ ≤ x := succ_order.succ_le_of_lt h_1,
    rw hj at hi,
    have hi' := mem_of_subset_of_mem hsupp hx,
    have hi' : ↑↑x < i := hi',
    have hi'' := not_le_of_lt hi',
    contradiction
  },

  by_cases hgood : a ⟨j, hjo⟩ ≠ 0,
  { -- Case: j is good
    let j_good : good := ⟨⟨j, hjo⟩, hgood⟩,
    by_cases hjsupp : j_good ∈ l.support,
    { let l' := l + finsupp.single j_good (-(l j_good)),
      have hsupp' : (l'.support : set good) ⊆ (λ x : good, x.1.1 < j),
      { have : j_good.1.1.succ = i := hj,
        exact support_remove this hsupp rfl
      },
      let lB := Exists.some (hB_BB j l' hsupp'),
      have hlBsupp : (lB.support : set {i // i < o}) ⊆ λ (x : {i // i < o}), x.1 < j :=
        (Exists.some_spec (hB_BB j l' hsupp')).1,
      have hlBtot : finsupp.total {i // i < o} M R B lB = finsupp.total good N R BB l' :=
       (Exists.some_spec (hB_BB j l' hsupp')).2,
      have h₁ : (B.coord ⟨j, hjo⟩) (finsupp.total good N R BB l) = 0 :=
        by simp only [hl, linear_map.map_zero, coe_zero],
      have h₂ : (B.coord ⟨j, hjo⟩) (finsupp.total good N R BB l') = 0,
      { rw ←hlBtot,
        simp only [basis.repr_total, basis.coord_apply],
        rw ←finsupp.not_mem_support_iff,
        apply not_mem_subset hlBsupp,
        have : ¬ (⟨j, hjo⟩ : ords).val < j := by simp; exact irrefl j,
        exact this
      },
      have h₃ : (B.coord ⟨j, hjo⟩) (finsupp.total good N R BB (finsupp.single j_good (-(l j_good)))) ≠ 0,
      have hlj : l j_good ≠ 0 := (l.3 j_good).1 hjsupp,
      { simp only [hlj, finsupp.total_single, coe_smul_of_tower, basis.coord_apply, linear_equiv.map_smulₛₗ, ring_hom.id_apply,
                   finsupp.coe_smul, pi.smul_apply, algebra.id.smul_eq_mul, ne.def, neg_eq_zero, mul_eq_zero, false_or],
        have := hcoordB j_good,
        rw basis.coord_apply at this,
        exact this
      },
      have hsum : (B.coord ⟨j, hjo⟩) (finsupp.total good N R BB l')
                  =   (B.coord ⟨j, hjo⟩) (finsupp.total good N R BB l)
                    + (B.coord ⟨j, hjo⟩) (finsupp.total good N R BB (finsupp.single j_good (-(l j_good)))) :=
        by simp [l', finsupp.single_neg, map_add_neg, map_neg],
      simp only [h₁, h₂, zero_add] at hsum,
      have hsum := eq.symm hsum,
      contradiction
    },
    { have hsub : (l.support : set good) ⊆ (λ x : good, x.1.1 < j),
      intros x hx,
      have hx : x ∈ l.support := hx,
      by_contradiction,
      have h : ¬ x.1.1 < j := h,
      have h := eq_or_lt_of_le (not_lt.1 h),
      cases h,
      { have : j_good = x := by simp [j_good, h_1],
        rw this at hjsupp,
        contradiction
      },
      { exact not_j_lt_x x j hx h_1 hj },
      exact H j hji (le_of_lt hjo) l hsub hl
    },
  },
  { -- Case: j is not good
    have hsub : (l.support : set good) ⊆ (λ x : good, x.1.1 < j),
    intros x hx,
    have hx : x ∈ l.support := hx,
    by_contradiction,
    have h : ¬ x.1.1 < j := h,
    have h := eq_or_lt_of_le (not_lt.1 h),
    cases h,
    { have hx' := x.2,
      have : x.1 = ⟨j, hjo⟩ := by simp [h_1],
      rw this at hx',
      contradiction
    },
    { exact not_j_lt_x x j hx h_1 hj },
    exact H j hji (le_of_lt hjo) l hsub hl
  },
  { -- induction base: i = 0
    have hi : i = 0 := not_not.1 hi,
    rw hi at hsupp,
    simp only [ordinal.not_lt_zero] at hsupp,
    have hsupp : (l.support : set good) ⊆ ∅ := hsupp,
    rw [subset_empty_iff, finset.coe_eq_empty] at hsupp,
    simp only [finsupp.support_eq_empty.1 hsupp, _root_.map_zero, zero_mem]
  }
end

-- Auxiliary lemma for proving the span property at successor ordinals.
lemma span_succ
  {N : submodule R M}
  {BB : { i // a i ≠ 0} → M}
  {i : ordinal}
  (hio : i ≤ o)
  (hlim : ¬ordinal.is_limit i)
  {B : basis {i // i < o} R M}
  (H : ∀ (k : ordinal), k < i → k ≤ o → ∀ (l : {i // i < o} →₀ R),
      (l.support : set {i // i < o}) ⊆ (λ x, x.1 < k) →
      finsupp.total { i // i < o} M R B l ∈ N →
      finsupp.total { i // i < o} M R B l ∈ submodule.span R (range BB))
  {l : { i // i < o} →₀ R}
  (hsupp : (l.support : set {i // i < o}) ⊆ (λ x, x.1 < i))
  (hl : finsupp.total { i // i < o} M R B l ∈ N)
  (hBB : ∀ i, ((B.repr (BB i)).support : set {i // i < o}) ⊆ (λ x, x.1 ≤ i))
  (hc : ∀ j : {i // i < o}, (i = j.1.succ) →
    ∃ r : R, (B.coord j) (finsupp.total {i // i < o} M R B l) = r •  a j)
   (hBBN : ∀ i, BB i ∈ N)
  (hBBa : ∀ j : { i // a i ≠ 0}, (B.coord j) (BB j) = a j) :
finsupp.total { i // i < o} M R B l ∈ submodule.span R (range BB) :=
begin
  let ords := { i  // i < o},
  let good := {i // a i ≠ 0},
  dsimp at hsupp,
  dsimp only [ordinal.is_limit] at hlim,
  repeat {push_neg at hlim},
  by_cases hi : i ≠ 0,
  rcases (hlim hi) with ⟨j, hj⟩,
  have hji : j < i := hj.1,
  have hjo : j < o := lt_of_lt_of_le hji hio,
  have hj : j.succ = i := le_antisymm (ordinal.succ_le.2 hj.1) hj.2,

  have not_j_lt_x : ∀ (x : ords), ∀ (j : ordinal), x ∈ l.support → j < x.1 → j.succ = i → false,
  { intros x j hx h_1 hj,
    have hi : j.succ ≤ x := succ_order.succ_le_of_lt h_1,
    rw hj at hi,
    have hi' := mem_of_subset_of_mem hsupp hx,
    have hi' : ↑x < i := hi',
    have hi'' := not_le_of_lt hi',
    contradiction
  },
  have hc := (hc ⟨j, hjo⟩ hj.symm),

  by_cases hgood : a ⟨j, hjo⟩ ≠ 0,
  { -- Case: j is good
    let j_good : good := ⟨⟨j, hjo⟩, hgood⟩,
    by_cases hjsupp : (⟨j, hjo⟩ : {i // i < o}) ∈ l.support,
    { let r := Exists.some hc,
      have hr : (B.coord ⟨j, hjo⟩) (finsupp.total {i // i < o} M R B l) = r • a ⟨j, hjo⟩ := Exists.some_spec hc,
      let l' := l - B.repr (r • (BB j_good)),
      have hsum : finsupp.total {i // i < o} M R B l' = finsupp.total {i // i < o} M R B l - r • (BB j_good) := by simp [l'],
      have hsum' : finsupp.total {i // i < o} M R B l = finsupp.total {i // i < o} M R B l' + r • (BB j_good) := by simp only [hsum, sub_add_cancel],
      rw hsum',
      have hsupp₀ : (l'.support : set {i // i < o}) ⊆ (λ x, x.1 < i),
      { have hBBj := hBB j_good,
        have hBBj' : (B.repr) (BB j_good) ∈ finsupp.supported R R (λ (x : ords), x.val < i),
        have hx : ∀ x : ords, x.1 ≤ j → x.1 < j.succ := λ x p, lt_of_le_of_lt p (ordinal.lt_succ_self j),
        rw hj at hx,
        intros y hy,
        have := mem_of_subset_of_mem hBBj hy,
        exact hx y (this : y.val ≤ j_good),
        intros x hx,
        let l₀ : finsupp.supported R R (λ x : ords, x.1 < i) := ⟨l, hsupp⟩,
        let BBj₀ : finsupp.supported R R (λ x : ords, x.1 < i) := ⟨B.repr (BB j_good), hBBj'⟩,
        let l'₀ : finsupp.supported R R (λ x : ords, x.1 < i) := l₀ - r • BBj₀,
        have hl' : l' = l'₀ :=
          by simp only [l', linear_equiv.map_smulₛₗ, ring_hom.id_apply, coe_sub, subtype.coe_mk, coe_smul_of_tower],
        have hl'' := (finsupp.mem_supported R l'₀.1).1 l'₀.2,
        simp only [subtype.val_eq_coe, ←hl'] at hl'',
        exact mem_of_subset_of_mem hl'' hx
        },
      have hsupp' : (l'.support : set {i // i < o}) ⊆ (λ x, x.1 < j),
      { intros x hx,
        by_contradiction,
        have h : ¬ x.1 < j := h,
        have h := eq_or_lt_of_le (not_lt.1 h),
        cases h,
        have hjx : x = ⟨j, hjo⟩ := by simp [h_1],
        have hx : x ∈ l'.support := hx,
        rw l'.mem_support_to_fun at hx,
        have hl' : l' x = 0,
        dsimp [l'],
        have hu := hBBa j_good,
        simp at hu,
        simp only [hu, hjx, linear_equiv.map_smulₛₗ, ring_hom.id_apply, finsupp.coe_smul, pi.smul_apply],
        rw ←hr,
        simp,
        contradiction,
        have hx := mem_of_subset_of_mem hsupp₀ hx,
        have hx : x.1 < i := hx,
        rw ←hj at hx,
        have := mt (not_covby_iff (ordinal.lt_succ_self j)).2 (not_not.2 (order.succ_eq_iff_covby.mp rfl)),
        push_neg at this,
        have := not_lt_of_ge (this x h_1),
        contradiction
      },
      have hl' : finsupp.total {i // i < o} M R B l' ∈ N,
      { dsimp [l'],
        simp,
        rw sub_eq_add_neg,
        apply N.add_mem' hl,
        simp,
        apply N.smul_mem' r,
        exact hBBN j_good
      },
      have h : finsupp.total {i // i < o} M R B l' ∈ submodule.span R (range BB) := H j hji (le_of_lt hjo) l' hsupp' hl',
      have hBBj : r • (BB j_good) ∈ submodule.span R (range BB) := submodule.smul_mem' (submodule.span R (range BB)) r (mem_of_subset_of_mem subset_span (⟨j_good, rfl⟩ : BB j_good ∈ range BB)),
      exact submodule.add_mem' (submodule.span R (range BB)) h hBBj
    },
    { have hsub : (l.support : set {i // i < o}) ⊆ (λ x, x.1 < j),
      intros x hx,
      have hx : x ∈ l.support := hx,
      by_contradiction,
      have h : ¬ x.1 < j := h,
      have h := eq_or_lt_of_le (not_lt.1 h),
      cases h,
      { have : (⟨j, hjo⟩ : {i // i < o}) = x := by simp only [h_1, subtype.val_eq_coe, subtype.coe_eta],
        rw this at hjsupp,
        contradiction
      },
      { exact not_j_lt_x x j hx h_1 hj },
      exact H j hji (le_of_lt hjo) l hsub hl
    },
  },
  { -- Case: j is not good
    have hgood := not_not.1 hgood,
    simp only [hgood, ideal.submodule_span_eq, singleton_zero, ideal.span_zero, ideal.mem_bot] at hc,
    have hsub : (l.support : set {i // i < o}) ⊆ (λ x, x.1 < j),
    intros x hx,
    have hx : x ∈ l.support := hx,
    by_contradiction,
    have h : ¬ x.1 < j := h,
    have h := eq_or_lt_of_le (not_lt.1 h),
    cases h,
    { have : (⟨j, hjo⟩ : {i // i < o}) = x := by simp only [h_1, subtype.val_eq_coe, subtype.coe_eta],
      simp only [basis.coord_apply, basis.repr_total] at hc,
      rw this at hc,
      cases hc,
      simp only [algebra.id.smul_eq_mul, mul_zero] at hc_h,
      have hx := (finsupp.mem_support_to_fun l x).1 hx,
      contradiction
    },
    { exact not_j_lt_x x j hx h_1 hj },
    exact H j hji (le_of_lt hjo) l hsub hl
  },
  { -- induction base: i = 0
    have hi : i = 0 := not_not.1 hi,
    rw hi at hsupp,
    simp only [ordinal.not_lt_zero] at hsupp,
    have hsupp : (l.support : set {i // i < o}) ⊆ ∅ := hsupp,
    rw [subset_empty_iff, finset.coe_eq_empty] at hsupp,
    rw finsupp.support_eq_empty.1 hsupp,
    simp only [finsupp.support_eq_empty.1 hsupp, _root_.map_zero, zero_mem]
  }
end

end aux_lemmas


-- Auxiliary lemma for comparing a span in a submodule with the span considered in the larger module.
lemma span_restrict
  (N : submodule R M) (s : set M) (hs : s ⊆ N.carrier) :
  ∀ x : N, x ∈ @submodule.span R N _ _ _ (N.carrier.restrict s) ↔
  (x : M) ∈ submodule.span R s :=
begin
  intro x,
  split,
  { simp only [submodule.mem_span],
    intros hx p hp,
    let s' : set N := N.carrier.restrict s,
    have hp' : s' ⊆ comap N.subtype p,
    intros y hy,
    exact_mod_cast mem_of_subset_of_mem hp (hy : s y),
    have := hx (submodule.comap N.subtype p) hp',
    simp only [mem_comap, submodule.coe_subtype] at this,
    exact this,
  },
  { simp only [submodule.mem_span],
    intros hx p hp,
    have hp' : s ⊆ ↑(map N.subtype p),
    intros y hy,
    simp only [map_coe, submodule.coe_subtype, mem_image, set_like.mem_coe],
    have hy' := mem_of_subset_of_mem hs hy,
    refine ⟨⟨y, hy'⟩, ⟨_, rfl⟩⟩,
    have hy'' : N.carrier.restrict s ⟨y, hy'⟩,
    simp only [restrict_apply, coe_mk],
    exact hy,
    exact_mod_cast mem_of_subset_of_mem hp hy'',
    have hx' := hx (submodule.map N.subtype p) hp',
    simp at hx',
    exact hx'
  }
end

-- Auxiliary lemma for comparing a span in a submodule with the span considered in the larger module,
-- in the special case where the spanning set is the range of a map.
lemma span_range_cod_restrict
  (N : submodule R M) {α : Type*} (f : α → M) (h : ∀ (x : α), f x ∈ N) :
∀ x : N, x ∈ @submodule.span R N _ _ _ (range (cod_restrict f N h)) ↔ (x : M) ∈ submodule.span R (range f) :=
begin
  have hr : range (cod_restrict f N _) = N.carrier.restrict (range f),
  ext x,
  simp,
  split,
  { rintro ⟨y, hy⟩,
    use y,
    have hy := congr_arg coe hy,
    rw [coe_cod_restrict_apply] at hy,
    exact hy,
    exact h
  },
  { rintro ⟨y, hy⟩,
    use y,
    ext,
    rw coe_cod_restrict_apply,
    exact hy
  },
  rw hr,
  apply span_restrict,
  rintro x ⟨a, rfl⟩,
  exact h a
end

-- Equivalent of basis.reindex_apply for sets of indices.
theorem basis.reindex_apply_image {ι ι' : Type*}
  (b : basis ι R M) (e : ι ≃ ι') (s : set ι') :
(b.reindex e) '' s = (b ∘ (e.symm)) '' s :=
begin
  ext x,
  split,
  all_goals {
    rintro ⟨y, ⟨hy, rfl⟩⟩,
    simp only [basis.reindex_apply, function.comp_app, mem_image],
    refine ⟨y, ⟨hy, rfl⟩⟩
  }
end

-- Lemma on supports of finsupps, useful for finsupp.induction.
lemma finsupp.support_single_add {α : Type*}
  {l : α →₀ M}
  {b : M} (hb : b ≠ 0)
  {i : α} (hi : i ∉ l.support)
  {s : set α}
  (h : (finsupp.support (finsupp.single i b + l) : set α) ⊆ s) :
(finsupp.support l : set α) ⊆ s :=
begin
  haveI := classical.type_decidable_eq α,
  intros x hx,
  by_cases hx' : x = i,
  { have H : (finsupp.single i b + l) i ≠ 0 :=
      by simpa only [finsupp.not_mem_support_iff.1 hi, finsupp.coe_add, pi.add_apply, finsupp.single_eq_same, add_zero, ne.def],
    -- note: squeeze_simp does not work with field notations
    rw hx',
    exact mem_of_subset_of_mem h ((finsupp.mem_support_to_fun _ i).2 H)
  },
  { have H : (finsupp.single i b + l) x ≠ 0,
    simp only [finsupp.single_eq_of_ne (ne.symm hx'), finsupp.coe_add, pi.add_apply, zero_add, ne.def],
    exact (finsupp.mem_support_to_fun _ x).1 hx,
    exact mem_of_subset_of_mem h (finsupp.mem_support_iff.2 H)
  }
end

-- Lemma on supports of finsupps, useful for finsupp.induction.
lemma finsupp.mem_support_of_support_single_add {α : Type*}
  {l : α →₀ M}
  {b : M} (hb : b ≠ 0)
  {i : α} (hi : i ∉ l.support)
  {s : set α}
  (h : (finsupp.support (finsupp.single i b + l) : set α) ⊆ s) :
i ∈ s :=
begin
  haveI := classical.type_decidable_eq α,
  have H : (finsupp.single i b + l) i ≠ 0 := by simpa only [finsupp.not_mem_support_iff.1 hi, finsupp.coe_add, pi.add_apply, finsupp.single_eq_same, add_zero,
  ne.def],
  exact mem_of_subset_of_mem h (finsupp.mem_support_iff.2 H)
end



/-- A submodule of a free module over a principal ideal domain is free. -/
theorem submodule.nonempty_basis_of_pid' [is_domain R] [is_principal_ideal_ring R]
  {ι : Type u}
  (b : basis ι R M) (N : submodule R M) :
  ∃ (B : Type (u+1)), nonempty (basis B R N) :=
begin
  haveI : decidable_eq M := classical.type_decidable_eq M,
  -- Set up the data.
  let r := classical.some (cardinal.ord_eq ι),
  haveI := classical.some (classical.some_spec (cardinal.ord_eq ι)),
  let o := ordinal.type r,
  let ords := {j : ordinal // j < o},
  let enum : ords → ι := λ i, ordinal.enum r i.1 i.2,

  let seg : ords → set ι :=  λ i, λ x, ¬r (enum i) x,  -- i.e. x ≤ i
  let F := λ i : ords, span R (image (coe_fn b) (seg i)),
  let U := λ i, (F i) ⊓ N,
  let V : ords → submodule R N := λ i, (F i).comap N.subtype,
  let V₁ : ordinal → submodule R N := λ i, dite (i < o) (λ p, V ⟨i, p⟩) (λ p, 0),
  have hU : ∀ i, U i ≤ N := λ i, inf_le_right,
  let ideal := λ i : ords, submodule.map (b.coord (enum i)) (U i),
  let a := λ i, generator (ideal i),
  let P := λ x, a x ≠ 0,
  have a_mem : Π i : ords, a i ∈ ideal i := λ i, generator_mem _,
  let u := λ i, Exists.some (a_mem i),
  have hu := λ i, Exists.some_spec (a_mem i),

  let B : basis ords R M := basis.reindex b (ordinal.typein_iso r).to_equiv,

  let good := {j : ords // a j ≠ 0},
  let BB : good → N := cod_restrict (λ i, u i.1) N (λ i, by {apply hU i.1, exact (hu i.1).1}),

  have hu' : ∀ j : good, (B.coord j) (BB j) = a j.1 := λ j, (hu j).2,

  -- Prove lemmas about the data which are useful as hypotheses to the auxiliary lemmas above.
  have hc : ∀ i : ordinal, ∀ l : ords →₀ R, finsupp.total ords M R B l ∈ N →
    ((l.support : set ords) ⊆ (λ x, x.1 < i)) →
    ∀ j : ords, (i = j.1.succ) →
    ∃ r : R, (B.coord j) (finsupp.total ords M R B l) = r •  a j,
  { intros i l hl hsupp j hij,
    have hI : (B.coord j) (⇑(finsupp.total ords M R ⇑B) l) ∈ ideal j,
    refine ⟨finsupp.total ords M R B l, ⟨_, _⟩⟩,
    dsimp [U],
    refine ⟨_, hl⟩,
    simp only [mem_span_set, basis.coe_reindex, set_like.mem_coe],
    use finsupp.map_domain B l,
    split,
    rw finsupp.map_domain_support_of_inj_on l (inj_on_of_injective (basis.injective B) _),
    simp only [B, finset.coe_image, basis.reindex_apply_image],
    have h : ((ordinal.typein_iso r).to_equiv.symm) '' (l.support : set ords) ⊆ seg j,
    simp only [equiv.subset_image, rel_iso.coe_fn_to_equiv],
    intros x hx,
    use enum x,
    have hxi := mem_of_subset_of_mem hsupp hx,
    have hxi : x.1 < i := hxi,
    rw hij at hxi,
    have hxj : x.1 ≤ j.1 := succ_order.le_of_lt_succ hxi,
    split,
    have goal : ¬r (enum j) (enum x),
    rwa ordinal.enum_le_enum,
    exact goal,
    simp only [ordinal.typein_iso, ordinal.typein_enum, subtype.val_eq_coe, rel_iso.coe_fn_mk, equiv.coe_fn_mk, subtype.coe_eta],
    rw image_comp,
    exact image_subset b h,
    simp only [ordinal.typein_iso, subtype.val_eq_coe, basis.coe_reindex, equiv.coe_fn_symm_mk],
    rw ←@finsupp.total_apply M M R _ _ _ (λ x, x) _,
    rw finsupp.total_map_domain,
    rw function.injective.of_comp_iff (basis.injective b),
    exact equiv.injective (ordinal.typein_iso r).to_equiv.symm,
    simpa only [B, ordinal.typein_iso],
    rw ←submodule.is_principal.span_singleton_generator (ideal j) at hI,
    rw submodule.is_principal.mem_iff_eq_smul_generator  at hI,
    rw submodule.is_principal.span_singleton_generator at hI,
    exact hI
  },

  have hBBN : ∀ i, (BB i : M) ∈ N := λ i, by {apply hU i.1, exact (hu i.1).1},

  have hBB : ∀ i, (BB i : M) ∈ F i,
  { intro i,
    simp [BB],
    have : U i ≤ F i := inf_le_left,
    rw ←set_like.coe_subset_coe at this,
    have hi : u i ∈ U i := (hu i).1,
    exact_mod_cast mem_of_subset_of_mem this hi
  },

  have hcoordB : ∀ i : good, (B.coord i) (BB i) ≠ 0 := λ i, by rw hu'; exact i.2,

  have hBB' : ∀ i, (finsupp.support ((B.repr) (BB i)) : set ords) ⊆ (λ x, x.1 ≤ i),
  { intros i x hx,
    have h := hBB i,
    rw mem_span_set at h,
    rcases h with ⟨l, ⟨hsupp, hl⟩⟩,
    simp [B] at hx,
    simp [BB] at hl,
    let l' := finsupp.comap_domain b l (inj_on_of_injective (basis.injective b) _),
    have hsupp' : (l.support : set M) ⊆ range ⇑b := subset.trans hsupp (set.image_subset_range b (seg i)),
    have hrepr := finsupp.total_comap_domain' (λ i, i) b l (inj_on_of_injective (basis.injective b) _) hsupp',
    have hrepr : (finsupp.total ι M R ((λ i, i) ∘ b)) l' = ∑ (i : M) in l.support, l i • i := hrepr,
    dsimp [finsupp.sum] at hl,
    rw ←hrepr at hl,
    rw ←hl at hx,
    simp [ordinal.typein_iso] at hx,
    rw [←ne.def, ←finsupp.mem_support_iff] at hx,
    have hx := mem_of_subset_of_mem hsupp hx,
    rw function.injective.mem_set_image (basis.injective b) at hx,
    have : ¬r (enum i) (ordinal.enum r ↑x x.2) := hx,
    dsimp [enum] at this,
    have henum := ordinal.enum_le_enum r x.2 i.1.2,
    simp at henum,
    exact henum.1 this
  },

  have hB_BB : ∀ i : ordinal, ∀ l : good →₀ R, ((l.support : set good) ⊆ λ x, x.1.1 < i) →
    ∃ lB : ords →₀ R, ((lB.support : set ords) ⊆ λ x, x.1 < i) ∧ finsupp.total ords M R B lB = finsupp.total good N R BB l,
  { intros i l,
    apply @finsupp.induction good R _ _ l,
    { intro _,
      use 0,
      simp only [finsupp.support_zero, finset.coe_empty, empty_subset, _root_.map_zero, coe_zero, eq_self_iff_true, and_self]
    },
    { intros j r l hj hr hl hl',
      have hlsupp := finsupp.support_single_add hr hj hl',
      have hl := hl hlsupp,
      rcases hl with ⟨lB, ⟨hlBsupp, hlBtot⟩⟩,
      use lB + r • B.repr (BB j),
      split,
      have hj' := finsupp.mem_support_of_support_single_add hr hj hl',
      have hj' : j.1.1 < i := hj',
      have hBBjsupp : (finsupp.support ((B.repr) (BB j)) : set ords) ⊆ (λ x, x.1 < i),
      { intros x hx,
        have := mem_of_subset_of_mem (hBB' j) hx,
        have : x.1 ≤ j := this,
        exact lt_of_le_of_lt this hj'
      },
      let lB₀ : finsupp.supported R R (λ x, x.1 < i : set ords) := ⟨lB, hlBsupp⟩,
      let BBj₀ : finsupp.supported R R (λ x, x.1 < i : set ords) := ⟨(B.repr) (BB j), hBBjsupp⟩,
      let l'₀ := lB₀ + r • BBj₀,
      exact l'₀.2,
      simp only [map_add, linear_map.map_smulₛₗ, ring_hom.id_apply,
                 finsupp.total_single, coe_add, coe_smul_of_tower, basis.total_repr, hlBtot],
      rw add_comm
    }
  },

  -- Prove linear independence.
  have HH₁ : ∀ j : ordinal, j ≤ o → ∀ (l : good →₀ R),
    (l.support : set good) ⊆ (λ x : good, x.1.1 < j) → (finsupp.total good N R BB) l = 0 → l = 0,
  { intros j hj,
    apply @ordinal.induction (λ j, j ≤ o → ∀ (l : good →₀ R),
      (l.support : set good) ⊆ (λ x : good, x.1.1 < j) → (finsupp.total good N R BB) l = 0 → l = 0),
    dsimp,
    intros i H hio l hsupp hl,
    by_cases hlim : ordinal.is_limit i,
    { exact lin_ind_limit hio hlim H hsupp hl },
    { exact lin_ind_succ hB_BB hcoordB hio hlim H hsupp hl },
    exact hj
  },

  have H₁ : linear_independent R BB,
  { rw linear_independent_iff,
    intros l hl,
    have hsupp : (l.support : set good) ⊆ (λ x : good, x.1.1 < o) := λ x _, x.1.2,
    exact HH₁ o (le_refl o) l hsupp hl
  },

  -- Prove the span property.
  have HH₂ : ∀ j : ordinal, j ≤ o → ∀ (l : ords →₀ R),
    (l.support : set ords) ⊆ (λ x, x.1 < j) → finsupp.total ords M R B l ∈ N → finsupp.total ords M R B l ∈ submodule.span R (range (λ i : good, u i.1)),
  { intros j hj,
    apply @ordinal.induction (λ k, k ≤ o → ∀ (l : {i // i < o} →₀ R),
      (l.support : set {i // i < o}) ⊆ (λ x, x.1 < k) → finsupp.total { i // i < o} M R B l ∈ N →
      finsupp.total { i // i < o} M R B l ∈ submodule.span R (range (λ i : good, u i.1))),
    dsimp,
    intros i H hio l hsupp hl,
    by_cases hlim : ordinal.is_limit i,
    { exact span_limit hio hlim H hsupp hl },
    { exact span_succ hio hlim H hsupp hl hBB' (hc i l hl hsupp) hBBN hu' },
    exact hj
  },

  have H₂ : submodule.span R (range BB) = ⊤,
  { rw submodule.eq_top_iff',
    intro x,
    let l := B.repr (x : M),
    have hl : finsupp.total ords M R B l ∈ N := by simp only [l, basis.total_repr]; exact x.2,
    have hx := HH₂ o (le_refl o) l _ hl,
    simp only [l, basis.total_repr] at hx,
    rw (span_range_cod_restrict N (λ i : good, u i.1) _ x),
    exact hx,
    intros y _,
    exact y.2
  },

  exact ⟨good, ⟨basis.mk H₁ H₂⟩⟩
end


@[instance]
theorem submodule.free_of_pid_of_free [is_domain R] [is_principal_ideal_ring R]
  {N : submodule R M}
  [module.free R M] :
module.free R N :=
begin
  have h := (submodule.nonempty_basis_of_pid' (module.free.choose_basis R M) N).some_spec,
  cases h,
  exact module.free.of_basis h
end
