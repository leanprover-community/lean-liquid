import free_pfpng.setup

.

noncomputable theory

open_locale classical

open category_theory
open opposite

universe u

lemma Profinite.mono_free'_to_condensed_free_pfpng_aux
  (S B : Profinite.{u}) (b : B) (T : discrete_quotient S)
  (t : S.to_Condensed.val.obj (op B) →₀ ℤ) :
let e : S.to_Condensed.val.obj (op B) →
    S.condensed_free_pfpng.val.obj (op B) :=
    λ f, (S.to_condensed_free_pfpng.val.app (op B) f),
    ι : S.to_Condensed.val.obj (op B) → S :=
      λ f, (ulift.down f).1 b in
    ((limits.limit.π (S.fintype_diagram ⋙ forget Fintype ⋙
      AddCommGroup.free' ⋙ Ab.ulift) T)
      (S.condensed_free_pfpng_specialize B b (free'_lift e t))).down
  = t.map_domain (T.proj ∘ ι) :=
begin
  dsimp,
  revert t,
  rw ← function.funext_iff,
  dsimp,
  change ulift.down ∘ _ = _,
  apply finsupp.fun_ext,
  { intros, simp only [function.comp_app, map_add, ulift.add_down,
      eq_self_iff_true, forall_const] },
  { intros, simp only [function.comp_app, map_zero, ulift.zero_down,
      finsupp.map_domain_add] },
  { intros,
    simp only [function.comp_app, finsupp.map_domain_single,
      free'_lift_eq_finsupp_lift],
    dsimp [Profinite.condensed_free_pfpng_specialize],
    simp only [← comp_apply],
    erw limits.limit.lift_π,
    simp only [finsupp.sum_single_index, zero_smul, one_zsmul],
    ext i,
    dsimp [Profinite.condensed_free_pfpng_specialize_cone,
      finsupp.single, Profinite.free_pfpng_π, Profinite.to_free_pfpng],
    erw ProFiltPseuNormGrp₁.limit_π_coe_eq,
    simp only [← comp_apply, category.assoc],
    dsimp [Profinite.free_pfpng_level_iso,
      limits.is_limit.cone_point_unique_up_to_iso],
    simp only [← comp_apply, category.assoc],
    erw (limits.is_limit_of_preserves (ProFiltPseuNormGrp₁.level.obj 1)
      (limits.limit.is_limit (S.fintype_diagram ⋙ free_pfpng_functor))).fac,
    erw limits.limit.lift_π,
    refl },
end

lemma Profinite.specialization_eq_zero_of_eq_zero (S B : Profinite.{u}) (b : B)
  (t : S.to_Condensed.val.obj (op B) →₀ ℤ)
  (ht : free'_lift (S.to_condensed_free_pfpng.val.app (op B)) t = 0) :
  t.map_domain (λ f, (ulift.down f).1 b) = 0 :=
begin
  apply free_pfpng.discrete_quotient_separates_points' S,
  intros T,
  apply_fun (λ e, S.condensed_free_pfpng_specialize B b e) at ht,
  rw add_monoid_hom.map_zero at ht,
  apply_fun (λ e, limits.limit.π (S.fintype_diagram ⋙ forget Fintype ⋙
    AddCommGroup.free' ⋙ Ab.ulift) T e) at ht,
  rw add_monoid_hom.map_zero at ht,
  apply_fun ulift.down at ht,
  dsimp [AddCommGroup.free'],
  rw ← finsupp.map_domain_comp,
  have := S.mono_free'_to_condensed_free_pfpng_aux B b T t,
  dsimp at this, erw ← this, exact ht
end

lemma Profinite.adj'_hom_equiv_symm_eq_free'_lift (S B : Profinite.{u}) :
    (((AddCommGroup.adj'.whisker_right Profinite.{u}ᵒᵖ).hom_equiv
      S.to_Condensed.val S.condensed_free_pfpng.val).symm
      S.to_condensed_free_pfpng.val).app (op B) =
    free'_lift (S.to_condensed_free_pfpng.val.app (op B)) :=
begin
  ext u v, dsimp [free'_lift],
  simp only [adjunction.hom_equiv_counit, whiskering_right_obj_map,
    nat_trans.comp_app, whisker_right_app,
    adjunction.whisker_right_counit_app_app],
end

open_locale big_operators
lemma finsupp.map_domain_ne_zero_of_ne_zero_of_inj_on {α β γ : Type*} [add_comm_group β]
  (t : α →₀ β) (ht : t ≠ 0) (f : α → γ)
  (hinj : set.inj_on f t.support) :
  t.map_domain f ≠ 0 :=
begin
  contrapose! ht,
  have : ∀ (e : γ) (he : e ∈ (t.map_domain f).support), ∃ (q : α) (hq : q ∈ t.support), f q = e,
  { intros e he, by_contra c, push_neg at c,
    simp only [finsupp.mem_support_iff, ne.def] at he,
    apply he,
    erw finset.sum_apply',
    apply finset.sum_eq_zero,
    intros a ha,
    dsimp [finsupp.single], rw if_neg, apply c, exact ha },
  choose q hq hh using this,
  let ι : (t.map_domain f).support → t.support :=
    λ e, ⟨q e.1 e.2, hq e.1 e.2⟩,
  have hι : function.surjective ι,
  { rintros ⟨e,he⟩, use f e,
    { simp only [finsupp.mem_support_iff, ne.def],
      rw finsupp.map_domain_apply' _ _ (set.subset.refl _) hinj he,
      simpa using he },
    { ext, dsimp,
      apply hinj, apply hq, apply he, apply hh } },
  have : (t.map_domain f).support = ∅, by simpa using ht,
  suffices : t.support = ∅, by simpa using this,
  by_contra c, change _ ≠ _ at c,
  erw ← finset.nonempty_iff_ne_empty at c,
  obtain ⟨c,hc⟩ := c, obtain ⟨⟨c,hc⟩,ee⟩ := hι ⟨c,hc⟩,
  rw this at hc, simpa using hc,
end

lemma finsupp.lift_map_domain {γ α β : Type*} [add_comm_group β]
  (f : α → β) (ι : γ → α) :
  (finsupp.lift _ ℤ _ f) ∘ finsupp.map_domain ι = finsupp.lift _ ℤ _ (f ∘ ι) :=
begin
  apply finsupp.fun_ext,
  { intros x y,
    dsimp only [function.comp_apply],
    simp only [finsupp.map_domain_add],
    erw ((finsupp.lift β ℤ α) f).to_add_monoid_hom.map_add, refl },
  { intros x y,
    erw ((finsupp.lift β ℤ γ) (f ∘ ι)).to_add_monoid_hom.map_add, refl },
  { intros x, simp },
end

lemma finsupp.lift_map_domain_apply {γ α β : Type*} [add_comm_group β]
  (f : α → β) (ι : γ → α) (e : γ →₀ ℤ) :
  (finsupp.lift _ ℤ _ f).to_add_monoid_hom (e.map_domain ι) =
  finsupp.lift _ ℤ _ (f ∘ ι) e :=
begin
  rw ← finsupp.lift_map_domain, refl,
end

lemma finsupp.card_supp_map_domain_lt {α β γ : Type*} [add_comm_group γ]
  (f : α → β) (t : α →₀ γ) (u v : α)
  (huv : u ≠ v) (hu : u ∈ t.support) (hv : v ∈ t.support)
  (hf : f u = f v) : (t.map_domain f).support.card < t.support.card :=
begin
  classical,
  have key : (finsupp.map_domain f t).support ⊆ _ := finsupp.map_domain_support,
  have : (finsupp.map_domain f t).support.card ≤ (t.support.image f).card :=
    finset.card_le_of_subset key,
  refine lt_of_le_of_lt this _,
  have key' : (t.support.image f).card ≤ t.support.card := finset.card_image_le,
  apply lt_of_le_of_ne key',
  change ¬ _,
  rw finset.card_image_iff,
  dsimp [set.inj_on],
  push_neg, use [u, hu, v, hv, hf],
end

lemma Profinite.mono_free'_to_condensed_free_pfpng_induction_aux (n : ℕ) :
  ∀ (S B : Profinite.{u}) (t : S.to_Condensed.val.obj (op B) →₀ ℤ),
    t.support.card ≤ n →
    (free'_lift (S.to_condensed_free_pfpng.val.app (op B))) t = 0 →
  (∀ (b : ↥B), finsupp.map_domain (λ f : S.to_Condensed.val.obj (op B),
    (ulift.down f).1 b) t = 0) →
  (∃ (α : Type u) [_inst_1 : fintype α] (X : α → Profinite) (π : Π (a : α), X a ⟶ B)
    (surj : ∀ (b : ↥B), ∃ (a : α) (x : ↥(X a)), (π a) x = b),
    ∀ (a : α), finsupp.map_domain (S.to_Condensed.val.map (π a).op) t = 0) :=
begin
  /-
  TODO: This proof is very slow. It would be better to pull out a few
  of the `have` statements into separate lemmas to (hopefully)
  speed this up.
  -/
  induction n,
  case nat.zero
  { intros S B t ht, simp at ht, rw ht, intros h1 h2,
    use [punit, infer_instance, λ _, B, λ _, 𝟙 _],
    split, { intros b, use [punit.star, b], refl },
    { intros _, rw finsupp.map_domain_zero, } },
  case nat.succ : n hn
  { intros S B t ht1 ht2 H,
    by_cases ht1' : t.support.card = n+1, swap,
    { apply hn, exact nat.le_of_lt_succ (nat.lt_of_le_and_ne ht1 ht1'),
      assumption' },
    clear ht1,
    let F := t.support,
    let e : F → (B ⟶ S) := λ f, f.1.1,
    obtain ⟨Q,h1,h2,ee,-⟩ : ∃ (α : Type u) (hα1 : fintype α)
      (hα2 : linear_order α) (ee : α ≃ F), true,
    { refine ⟨ulift (fin (fintype.card F)), infer_instance,
        is_well_order.linear_order well_ordering_rel,
        equiv.ulift.trans (fintype.equiv_fin _).symm, trivial⟩, },
    resetI,
    let E₀ := { a : Q × Q | a.1 < a.2 },
    let X₀ : E₀ → Profinite.{u} := λ i, Profinite.equalizer (e (ee i.1.1)) (e (ee i.1.2)),
    let π₀ : Π (i : E₀), X₀ i ⟶ B := λ i, Profinite.equalizer.ι _ _,

    have surj₀ : ∀ (b : B), ∃ (e₀ : E₀) (x : X₀ e₀), π₀ _ x = b,
    { intro b, specialize H b,
      contrapose! H,
      have key : ∀ (i j : Q) (h : i < j), e (ee i) b ≠ e (ee j) b,
      { intros i j h, specialize H ⟨⟨i,j⟩, h⟩, intro c,
        specialize H, dsimp [X₀] at H, specialize H ⟨b, c⟩,
        apply H, refl },
      apply finsupp.map_domain_ne_zero_of_ne_zero_of_inj_on,
      { intro c, rw c at ht1', simpa using ht1' },
      { intros x hx y hy hxy, dsimp at hxy,
        let i : Q := ee.symm ⟨x,hx⟩,
        let j : Q := ee.symm ⟨y,hy⟩,
        rcases lt_trichotomy i j with (hhh|hhh|hhh),
        { specialize key i j hhh, contrapose hxy, convert key,
          { dsimp [i], rw ee.apply_symm_apply, refl },
          { dsimp [j], rw ee.apply_symm_apply, refl } },
        { apply_fun (λ q, (ee q).1) at hhh, dsimp [i,j] at hhh,
          simp_rw ee.apply_symm_apply at hhh, exact hhh },
        { specialize key j i hhh, contrapose hxy, convert key.symm,
          { dsimp [j], rw ee.apply_symm_apply, refl },
          { dsimp [i], rw ee.apply_symm_apply, refl } } } },

    let f₀ : Π (i : E₀), S.to_Condensed.val.obj (op B) → S.to_Condensed.val.obj (op (X₀ i)) :=
      λ i, S.to_Condensed.val.map (π₀ i).op,

    let t₀ : Π (i : E₀), S.to_Condensed.val.obj (op (X₀ i)) →₀ ℤ :=
      λ i, t.map_domain (f₀ i),

    have card₀ : ∀ (i : E₀), (t₀ i).support.card ≤ n,
    { intros i, suffices : (t₀ i).support.card < n + 1,
        by exact nat.lt_succ_iff.mp this,
      rw ← ht1',
      fapply finsupp.card_supp_map_domain_lt,
      refine (ee i.1.1).1,
      refine (ee i.1.2).1,
      { change ¬ _,
        erw ← subtype.ext_iff,
        apply ee.injective.ne,
        apply ne_of_lt,
        exact i.2 },
      refine (ee i.1.1).2,
      refine (ee i.1.2).2,
      { dsimp [f₀, π₀, Profinite.to_Condensed], ext1, dsimp,
        -- missing Profinite.equalizer.condition
        ext t, exact t.2 } },

    have lift₀ : ∀ (i : E₀), free'_lift (S.to_condensed_free_pfpng.val.app (op (X₀ i))) (t₀ i) = 0,
    { intros i, rw free'_lift_eq_finsupp_lift, dsimp only [t₀, f₀],
      apply_fun (λ q, S.condensed_free_pfpng.val.map (π₀ i).op q) at ht2,
      rw [add_monoid_hom.map_zero, free'_lift_eq_finsupp_lift] at ht2,
      convert ht2,
      rw finsupp.lift_map_domain_apply,
      dsimp [finsupp.lift],
      rw (S.condensed_free_pfpng.val.map (π₀ i).op).map_finsupp_sum,
      refl },

    have map₀ : ∀ (i : E₀) (b : ↥(X₀ i)),
        finsupp.map_domain
          (λ (f : S.to_Condensed.val.obj (op (X₀ i))), f.down.to_fun b) (t₀ i) = 0,
    { intros i b, dsimp [t₀], rw ← finsupp.map_domain_comp,
      exact H (π₀ i b) },

    have key := λ i, hn S (X₀ i) (t₀ i) (card₀ i) (lift₀ i) (map₀ i),

    choose A hA X₁ π₁ surj₁ key using key, resetI,

    let E := Σ (e : E₀), A e,
    let X : E → Profinite.{u} := λ i, X₁ i.1 i.2,
    let π : Π (e : E), X e ⟶ B := λ e, π₁ e.1 e.2 ≫ π₀ e.1,

    use [E, infer_instance, X, π], split,

    { intros b,
      obtain ⟨e₀,x,hx⟩ := surj₀ b,
      obtain ⟨i,q,hq⟩ := surj₁ e₀ x,
      use [⟨e₀,i⟩,q], dsimp [π], rw [hq, hx] },
    { intros a,
      dsimp [π], rw functor.map_comp,
      erw finsupp.map_domain_comp,
      apply key } },
end

instance Profinite.mono_free'_to_condensed_free_pfpng
  (S : Profinite.{u}) : mono S.free'_to_condensed_free_pfpng :=
begin
  apply presheaf_to_Condensed_Ab_map_mono_of_exists, intros B t ht,
  let e : S.to_Condensed.val.obj (op B) →
    S.condensed_free_pfpng.val.obj (op B) :=
    λ f, (S.to_condensed_free_pfpng.val.app (op B) f),
  dsimp at t ht,
  replace ht : free'_lift e t = 0, by rwa ← S.adj'_hom_equiv_symm_eq_free'_lift,
  let ι : Π b : B, S.to_Condensed.val.obj (op B) → S :=
    λ b f, (ulift.down f).1 b,
  have aux : ∀ b : B, t.map_domain (ι b) = 0 :=
    λ b, S.specialization_eq_zero_of_eq_zero B b t ht,
  dsimp,
  apply Profinite.mono_free'_to_condensed_free_pfpng_induction_aux,
  refl,
  assumption',
end
