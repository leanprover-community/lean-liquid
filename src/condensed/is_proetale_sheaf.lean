import condensed.proetale_site
import for_mathlib.presieve
import topology.category.Profinite.projective
import for_mathlib.Profinite.disjoint_union
import for_mathlib.fintype_induction
import tactic.derive_fintype -- for pbool

universes w v u

namespace category_theory.functor

open category_theory opposite

variables {C : Type u} [category.{v} C] (Q : Profinite.{w}ᵒᵖ ⥤ C)
variables (P : Profinite.{w}ᵒᵖ ⥤ Type u)

/-- A presheaf of types `P` on `Profinite` satisfies the finite product
condition if given any finite collection of topological spaces `X i`
indexed by `i` in `(α : Fintype)`, the map from `P (∑ i, X i)`
to `Π (a : α), P (X a)` sending `x` to the dependent function sending
`a : α` to  `P (the inclusion X a → Σ i, X i), evaluated at x`,
is a bijection. -/
def finite_product_condition : Prop := ∀
(α : Fintype.{w}) (X : α → Profinite.{w}),
function.bijective (λ (x : P.obj (op (Profinite.sigma X))) (a : α),
  P.map (Profinite.sigma.ι X a).op x)

def finite_product_condition_of (α : Fintype.{w}) : Prop :=
  ∀ (X : α → Profinite.{w}),
  function.bijective (λ (x : P.obj (op (Profinite.sigma X))) (a : α),
    P.map (Profinite.sigma.ι X a).op x)

def finite_product_condition' : Prop := ∀
(n : ℕ) (X : ulift.{w} (fin n) → Profinite.{w}),
function.bijective (λ (x : P.obj (op (Profinite.sigma X))) (a : ulift (fin n)),
  P.map (Profinite.sigma.ι X a).op x)

namespace finite_product_aux
def obj_equiv {α β : Type*} (e : α ≃ β) (X : β → Profinite.{w}) (b : β) :
  X b ≅ X (e (e.symm b)) := eq_to_iso (congr_arg X (e.apply_symm_apply _).symm)

def product_equiv {α β : Type*} (e : α ≃ β) (X : β → Profinite.{w}) :
  (Π (a : α), P.obj (opposite.op (X (e a)))) ≃ (Π b, P.obj (opposite.op (X b))) :=
e.Pi_congr (λ b, equiv.refl _)

def sigma_equiv {α β : Type w} [fintype α] [fintype β] (e : α ≃ β) (X : β → Profinite.{w}) :
  P.obj (opposite.op (Profinite.sigma (X ∘ e))) ≃
  P.obj (opposite.op (Profinite.sigma X)) :=
(P.map_iso (Profinite.sigma_iso_of_equiv _ _).op).symm.to_equiv

lemma product_equiv_compatible {α β : Type w} [fintype α] [fintype β]
  (e : α ≃ β) (X : β → Profinite.{w}) (a) (b) :
    P.map (Profinite.sigma.ι _ b).op ((sigma_equiv P e X).symm a) =
    (product_equiv P e X).symm (λ b, P.map (Profinite.sigma.ι _ _).op a) b :=
begin
  dsimp [product_equiv, sigma_equiv],
  simp only [← functor_to_types.map_comp_apply],
  refl,
end

end finite_product_aux

open finite_product_aux

lemma finite_product_condition_of_equiv (α β : Fintype.{w}) (e : α ≃ β)
  (h : P.finite_product_condition_of α) : P.finite_product_condition_of β :=
begin
  intros X,
  specialize h (X ∘ e),
  let f := _, show function.bijective f,
  let g := _, change function.bijective g at h,
  have : f = (product_equiv _ _ _) ∘ g ∘ (sigma_equiv P e X).symm,
  { suffices : (product_equiv _ _ _).symm ∘ f = g ∘ (sigma_equiv P e X).symm,
    by { rw ← this, ext, simp },
    symmetry,
    ext a,
    apply product_equiv_compatible },
  rw this,
  apply function.bijective.comp (equiv.bijective _) (h.comp (equiv.bijective _))
end

lemma finite_product_condition_iff_finite_product_condition' :
  P.finite_product_condition ↔ P.finite_product_condition' :=
begin
  split,
  { intros h n X,
    apply h ⟨ulift (fin n)⟩ X },
  { intros h α X,
    let n := fintype.card α,
    let e : ulift.{w} (fin n) ≃ α := equiv.ulift.trans (fintype.equiv_fin _).symm,
    let f := _, show function.bijective f,
    specialize h n (X ∘ e),
    let g := _, change function.bijective g at h,
    have : f = (product_equiv _ _ _) ∘ g ∘ (sigma_equiv P e X).symm,
    { suffices : (product_equiv _ _ _).symm ∘ f = g ∘ (sigma_equiv P e X).symm,
        by { rw ← this, ext, simp },
      symmetry,
      ext a,
      apply product_equiv_compatible },
    rw this,
    apply function.bijective.comp (equiv.bijective _) (h.comp (equiv.bijective _)) }
end

def empty_condition : Prop :=
  function.bijective (λ t : P.obj (op Profinite.empty), punit.star.{u})

def product_condition : Prop := ∀ (X Y : Profinite.{w}),
  function.bijective (λ (t : P.obj (op $ Profinite.sum X Y)),
    ((P.map (Profinite.sum.inl X Y).op t, P.map (Profinite.sum.inr X Y).op t) :
      P.obj (op X) × P.obj (op Y)))

lemma finite_product_condition_of_empty_iff_empty_condition :
  P.finite_product_condition_of ⟨pempty⟩ ↔ P.empty_condition := sorry

lemma finite_product_condition_of_pair_iff_product_condition :
  P.finite_product_condition_of ⟨limits.walking_pair⟩ ↔ P.product_condition := sorry

open opposite

lemma finite_product_condition_of_sum (α β : Fintype.{w})
  (h1 : P.product_condition)
  (h2 : P.finite_product_condition_of α) :
  P.finite_product_condition_of (Fintype.of $ α ⊕ (punit : Type w)) :=
begin
  intros X,
  let f := _, show function.bijective f,
  let I : Profinite.sigma X ≅ _ := Profinite.sigma_sum_iso' _,
  let t : P.obj (opposite.op (Profinite.sigma X)) ≃ _ :=
    (P.map_iso I.symm.op).to_equiv,
  specialize h1 (Profinite.sigma (X ∘ sum.inl)) (Profinite.sigma (X ∘ sum.inr)),
  let g := _, change function.bijective g at h1,
  let e : (Π (a : ↥(Fintype.of (↥α ⊕ punit))), P.obj (opposite.op (X a))) ≃
    (Π (a : α), P.obj (op (X (sum.inl a)))) × P.obj (op (X (sum.inr punit.star))) :=
    ⟨ λ f, ⟨λ a, f (sum.inl a), f (sum.inr _)⟩,
      λ f x, sum.rec_on x (λ a, f.1 a) (λ ⟨⟩, f.2), _, _⟩,
  rotate, { sorry }, { sorry },
  let l : P.obj (op (X (sum.inr punit.star))) ≃ P.obj (op (Profinite.sigma (X ∘ sum.inr))) :=
    (P.map_iso (Profinite.sigma_punit_iso (X ∘ sum.inr)).op).symm.to_equiv,
  specialize h2 (X ∘ sum.inl),
  let p := _, change function.bijective p at h2,
  let q :
    P.obj (op (Profinite.sigma (X ∘ sum.inl))) × P.obj (op (Profinite.sigma (X ∘ sum.inr)))
      → (Π (a : α), P.obj (op (X (sum.inl a)))) × P.obj (op (Profinite.sigma (X ∘ sum.inr))) :=
    prod.map p id,
  have hq : function.bijective q := sorry,
  let r : (Π (a : α), P.obj (op (X (sum.inl a)))) × _ → _ × _ := prod.map id l.symm,
  have hr : function.bijective r := sorry,
  have : f = e.symm ∘ prod.map id l.symm ∘ q ∘ g ∘ t, sorry,
  rw this,
  exact e.symm.bijective.comp (hr.comp (hq.comp (h1.comp t.bijective))),
end

theorem finite_product_condition_iff_empty_product :
  P.finite_product_condition ↔ P.empty_condition ∧ P.product_condition :=
begin
  split,
  { intros h,
    split,
    rw ← finite_product_condition_of_empty_iff_empty_condition,
    apply h,
    rw ← finite_product_condition_of_pair_iff_product_condition,
    apply h },
  { rintros ⟨h1,h2⟩,
    have := @Fintype.induction_empty_sum (λ (α : Fintype.{w}), P.finite_product_condition_of α),
    apply this,
    { intros α β e h,
      apply finite_product_condition_of_equiv _ _ _ e h },
    { erw finite_product_condition_of_empty_iff_empty_condition,
      assumption },
    { intros α h,
      apply finite_product_condition_of_sum P α (Fintype.of punit),
      assumption,
      assumption } }
end

-- should this be in mathlib in some form?
section is_singleton

-- is_singleton X is [nonempty X] [subsingleton X]

theorem is_singleton_iff_forall_bijective_to_punit (X : Sort*) :
  nonempty X ∧ subsingleton X ↔ ∀ f : X → punit, function.bijective f :=
begin
  split,
  { rintro ⟨h1, h2⟩ f,
    haveI := h2,
    exact ⟨λ a b h, subsingleton.elim _ _, λ s, ⟨h1.some, subsingleton.elim _ _⟩⟩ },
  { intro h,
    cases h (λ x, punit.star) with finj fsurj,
    choose g hg using fsurj,
    refine ⟨⟨g punit.star⟩, subsingleton.intro $ λ a b, finj rfl⟩, }
end

theorem is_singleton_iff_forall_bijective_to_is_singleton (X : Sort*) :
  nonempty X ∧ subsingleton X ↔ ∀ (Y : Sort*) [nonempty Y] [subsingleton Y]
  (f : X → Y), function.bijective f :=
begin
  split,
  { rintro ⟨⟨x⟩, hx⟩ Y hY1 hY2 f,
    haveI := hY2,
    haveI := hx,
    refine ⟨λ a b h, subsingleton.elim a b, λ s, ⟨x, subsingleton.elim _ _⟩⟩ },
  { intro h,
    cases h punit (λ x, punit.star) with finj fsurj,
    choose g hg using fsurj,
    refine ⟨⟨g punit.star⟩, subsingleton.intro $ λ a b, finj rfl⟩, }
end

theorem is_singleton_iff_exists_bijective_to_punit (X : Sort*) :
  nonempty X ∧ subsingleton X ↔ ∃ f : X → punit, function.bijective f :=
begin
  split,
  { rintro ⟨⟨x⟩, hx⟩,
    haveI := hx,
    use (λ x, punit.star),
    refine ⟨λ a b _, subsingleton.elim a b,
      λ a, ⟨x, subsingleton.elim _ _⟩⟩ },
  { rintro ⟨f, finj, fsurj⟩,
    choose g hg using fsurj,
    refine ⟨⟨g punit.star⟩, subsingleton.intro $ λ a b, finj $ subsingleton.elim _ _⟩, }
end

theorem is_singleton_iff_exists_bijective_to_is_singleton (X : Sort*) :
  nonempty X ∧ subsingleton X ↔ ∃ (Y : Sort*) [nonempty Y] [subsingleton Y] (f : X → Y), function.bijective f :=
begin
  split,
  { rintro ⟨⟨x⟩, hx⟩,
    haveI := hx,
    use [punit, infer_instance, infer_instance, (λ x, punit.star)],
    refine ⟨λ a b _, subsingleton.elim a b,
      λ a, ⟨x, subsingleton.elim _ _⟩⟩ },
  { rintro ⟨Y, hY1, hY2, f, finj, fsurj⟩,
    choose g hg using fsurj,
    haveI := hY2,
    refine ⟨⟨g hY1.some⟩, ⟨λ a b, finj $ subsingleton.elim _ _⟩⟩, },
end

lemma subsingleton.map_equiv {X Y : Type*} (e : X ≃ Y) : subsingleton X → subsingleton Y :=
λ h, ⟨λ a b, e.symm.injective $ @subsingleton.elim _ h _ _⟩

end is_singleton

section pbool

-- The category theory library has a type called `walking_pair` which accomplishes the same thing.
-- It's used in the API for binary (co)products.

@[derive fintype]
inductive pbool : Type u
| ff : pbool
| tt : pbool

end pbool

-- Kevin is working on this
lemma finite_product_condition_iff_empty_condition_product_condition :
  P.finite_product_condition ↔ P.empty_condition ∧ P.product_condition :=
begin
  split,
  { intro h_prod,
    split,
    { specialize h_prod (Fintype.of pempty) (λ x, Profinite.empty),
      suffices hs : nonempty (P.obj (op Profinite.empty)) ∧ subsingleton (P.obj (op Profinite.empty)),
      { rw is_singleton_iff_forall_bijective_to_punit at hs,
        apply hs },
      let e : Profinite.sigma.{w} (λ (x : ↥(Fintype.of.{w} pempty)), Profinite.empty) ≅ Profinite.empty :=
      { hom := Profinite.sigma.desc _ (λ i, by cases i),
        inv := Profinite.empty.elim _,
        hom_inv_id' := by {ext1 x, rcases x with ⟨⟨⟩⟩ },
        inv_hom_id' := by {ext1 x, cases x } },
      let e2 := category_theory.iso.op e,
      let e3 := category_theory.functor.map_iso P e2,
      let e4 := category_theory.iso.to_equiv e3,
      have := (is_singleton_iff_exists_bijective_to_is_singleton _).2 ⟨_, _, _, _, h_prod⟩,
      { exact ⟨nonempty.map e4.symm this.1, subsingleton.map_equiv e4.symm this.2⟩ },
      { exact ⟨λ x, by rcases x with ⟨⟨⟩⟩⟩ },
      { exact ⟨λ f g, by {ext x, rcases x with ⟨⟨⟩⟩ }⟩ } },
    { specialize h_prod (Fintype.of pbool),
      /-
      ∀ (X : ↥(Fintype.of pbool)) → Profinite), function.bijective
       (λ (x : P.obj (opposite.op (Profinite.sigma X))) (a : ↥(Fintype.of pbool)), P.map (Profinite.sigma.ι X a).op x)

      For all X : pbool -> Profinite, the obvious map from
      P(Σ X) to Π (a : pbool), P (X a) is bijective
      -/
      intros S T,
      let X : ↥(Fintype.of pbool) → Profinite :=
        λ a, pbool.rec S T a,
      specialize h_prod X,
      /-
      hypothesis : if X : pbool -> Profinite sends ff to S
      and tt to T, then the obvious map from
      P(Σ X) to Π (a : pbool), P (X a) is bijective.

      Goal: the obvious map from P (S ⊕ T) to P S × P T is bijective

      plan : triangle S → Σ X ≃ S ⊕ T commutes;
      triangle T → Σ X ≃ S ⊕ T commutes;

      Claim: the obvious map from P (S ⊕ T) to P S × P T
      is the obvious map from P (S ⊕ T) to Π (a : pbool), P (X a)
      composed with the obvious bijection
        from Π a, P (X a) to P S × P T.

      Reid says work with the commutative square, i.e. the two maps
      P (Σ a, X a) ⟶ P S × P T

      -/
      sorry
    } },
  { sorry }
end

def map_to_equalizer {W X B : Profinite.{w}} (f : X ⟶ B) (g₁ g₂ : W ⟶ X)
  (w : g₁ ≫ f = g₂ ≫ f) :
  P.obj (op B) → { x : P.obj (op X) | P.map g₁.op x = P.map g₂.op x } :=
λ t, ⟨P.map f.op t, by { change (P.map _ ≫ P.map _) _ = (P.map _ ≫ P.map _) _,
  simp_rw [← P.map_comp, ← op_comp, w] }⟩

def equalizer_condition : Prop := ∀
(X B : Profinite.{w}) (π : X ⟶ B) (surj : function.surjective π),
function.bijective (map_to_equalizer P π (Profinite.pullback.fst π π) (Profinite.pullback.snd π π)
    (Profinite.pullback.condition _ _))

-- Should we make this `unique` instead of `subsingleton`?
def subsingleton_empty : Prop := ∀
(Z : Profinite.{w}) [is_empty Z], subsingleton (P.obj (op Z))

def is_proetale_sheaf_of_types : Prop := ∀
-- a finite family of morphisms with base B
(α : Type w) [fintype α] (B : Profinite.{w}) (X : α → Profinite.{w}) (f : Π a, X a ⟶ B)
-- jointly surjective
(surj : ∀ b : B, ∃ a (x : X a), f a x = b)
-- family of terms
(x : Π a, P.obj (op (X a)))
-- which is compatible
(compat : ∀ (a b : α) (Z : Profinite.{w}) (g₁ : Z ⟶ X a) (g₂ : Z ⟶ X b),
  (g₁ ≫ f a = g₂ ≫ f b) → P.map g₁.op (x a) = P.map g₂.op (x b)),
-- the actual condition
∃! t : P.obj (op B), ∀ a : α, P.map (f a).op t = x a

def is_proetale_sheaf_of_types_pullback : Prop := ∀
-- a finite family of morphisms with base B
(α : Type w) [fintype α] (B : Profinite.{w}) (X : α → Profinite.{w}) (f : Π a, X a ⟶ B)
-- jointly surjective
(surj : ∀ b : B, ∃ a (x : X a), f a x = b)
-- family of terms
(x : Π a, P.obj (op (X a)))
-- which is compatible
(compat : ∀ (a b : α),
  P.map (limits.pullback.fst : limits.pullback (f a) (f b) ⟶ _).op (x a) =
  P.map limits.pullback.snd.op (x b)),
-- the actual condition
∃! t : P.obj (op B), ∀ a : α, P.map (f a).op t = x a

def is_proetale_sheaf_of_types_explicit_pullback : Prop := ∀
-- a finite family of morphisms with base B
(α : Type w) [fintype α] (B : Profinite.{w}) (X : α → Profinite.{w}) (f : Π a, X a ⟶ B)
-- jointly surjective
(surj : ∀ b : B, ∃ a (x : X a), f a x = b)
-- family of terms
(x : Π a, P.obj (op (X a)))
-- which is compatible
(compat : ∀ (a b : α),
  P.map (Profinite.pullback.fst (f a) (f b)).op (x a) =
  P.map (Profinite.pullback.snd _ _).op (x b)),
-- the actual condition
∃! t : P.obj (op B), ∀ a : α, P.map (f a).op t = x a

def is_proetale_sheaf_of_types_projective : Prop := ∀
-- a finite family of projective objects
(α : Fintype.{w}) (X : α → Profinite.{w}) [∀ a, projective (X a)],
function.bijective (λ (x : P.obj (op $ Profinite.sigma X)) (a : α),
  P.map (Profinite.sigma.ι _ a).op x)

theorem subsingleton_empty_of_is_proetale_sheaf_of_types
  (h : P.is_proetale_sheaf_of_types) : P.subsingleton_empty :=
begin
  intros Z hZ,
  specialize h pempty Z pempty.elim (λ a, a.elim) hZ.elim (λ a, a.elim) (λ a, a.elim),
  obtain ⟨t,ht1,ht2⟩ := h,
  constructor,
  intros x y,
  have : x = t, { apply ht2, exact λ a, a.elim },
  have : y = t, { apply ht2, exact λ a, a.elim },
  cc,
end

theorem finite_product_condition_of_is_proetale_sheaf_of_types
  (h : P.is_proetale_sheaf_of_types) : P.finite_product_condition :=
begin
  intros α X,
  split,
  { intros x y hh,
    dsimp at hh,
    specialize h α (Profinite.sigma X) X (Profinite.sigma.ι X)
      (Profinite.sigma.ι_jointly_surjective X)
      (λ a, P.map (Profinite.sigma.ι X a).op x) _,
    { intros a b Z g₁ g₂ hhh,
      dsimp,
      change (P.map _ ≫ P.map _) _ = (P.map _ ≫ P.map _) _,
      simp_rw [← P.map_comp, ← op_comp, hhh] },
    obtain ⟨t,ht1,ht2⟩ := h,
    have hx : x = t,
    { apply ht2,
      intros a,
      refl },
    have hy : y = t,
    { apply ht2,
      intros a,
      apply_fun (λ e, e a) at hh,
      exact hh.symm },
    rw [hx, ← hy] },
  { intros bb,
    dsimp,
    specialize h α (Profinite.sigma X) X (Profinite.sigma.ι X)
      (Profinite.sigma.ι_jointly_surjective X) bb _,
    { intros a b Z g₁ g₂ hhh,
      by_cases hZ : is_empty Z,
      { haveI := hZ,
        haveI := subsingleton_empty_of_is_proetale_sheaf_of_types P h Z,
        apply subsingleton.elim },
      simp at hZ,
      obtain ⟨z⟩ := hZ,
      have : a = b,
      { apply_fun (λ e, (e z).1) at hhh,
        exact hhh },
      subst this,
      have : g₁ = g₂,
      { ext1 t,
        apply_fun (Profinite.sigma.ι X a),
        swap, { exact Profinite.sigma.ι_injective X a },
        apply_fun (λ e, e t) at hhh,
        exact hhh },
      rw this },
    obtain ⟨t,ht1,ht2⟩ := h,
    use t,
    ext,
    apply ht1 }
end

theorem is_proetale_sheaf_of_types_iff :
  P.is_proetale_sheaf_of_types ↔ presieve.is_sheaf proetale_topology P :=
begin
  erw presieve.is_sheaf_pretopology,
  split,
  { intros h B S hS,
    obtain ⟨α, _, X, f, surj, rfl⟩ := hS,
    resetI,
    intros x hx,
    dsimp [presieve.family_of_elements] at x,
    let y : Π (a : α), P.obj (op (X a)) := λ a, x (f a) _,
    swap,
    { rw presieve.mem_of_arrows_iff, use [a, rfl], simp },
    specialize h α B X f surj y _,
    { intros a b Z g₁ g₂ hh,
      dsimp [presieve.family_of_elements.compatible] at hx,
      apply hx,
      assumption },
    convert h,
    ext t,
    split,
    { intro hh,
      intros a,
      apply hh },
    { intros hh Y g hg,
      rw presieve.mem_of_arrows_iff at hg,
      obtain ⟨u,rfl,rfl⟩ := hg,
      simp [hh] } },
  { introsI h α _ B X f surj x compat,
    let R : presieve B := presieve.of_arrows X f,
    have hR : R ∈ proetale_pretopology B := ⟨α, infer_instance, X, f, surj, rfl⟩,
    have hhh : ∀ ⦃Y⦄ (g : Y ⟶ B) (hg : R g), ∃ (a : α) (ha : Y = X a), g = eq_to_hom ha ≫ f a,
    { intros Y g hg,
      rcases hg with ⟨a⟩,
      use [a, rfl],
      simp },
    let aa : Π ⦃Y⦄ (g : Y ⟶ B) (hg : R g), α := λ Y g hg, (hhh g hg).some,
    have haa : ∀ ⦃Y⦄ (g : Y ⟶ B) (hg : R g), Y = X (aa g hg) :=
      λ Y g hg, (hhh g hg).some_spec.some,
    have haa' : ∀ ⦃Y⦄ (g : Y ⟶ B) (hg : R g), g = eq_to_hom (haa g hg) ≫ f (aa g hg) :=
      λ Y g hg, (hhh g hg).some_spec.some_spec,
    let y : R.family_of_elements P := λ Y g hg, P.map (eq_to_hom (haa g hg)).op (x (aa g hg)),
    specialize h R hR y _,
    { rintros Y₁ Y₂ Z g₁ g₂ f₁ f₂ ⟨a⟩ ⟨b⟩ hh,
      change (P.map _ ≫ P.map _) _ = (P.map _ ≫ P.map _) _,
      simp_rw [← P.map_comp, ← op_comp],
      apply compat,
      simp_rw category.assoc,
      convert hh,
      all_goals {
        symmetry,
        apply haa' } },
    convert h,
    ext t,
    split,
    { intros hh Y g hg,
      conv_lhs { rw haa' g hg },
      dsimp [y],
      simp [hh] },
    { intros hh a,
      have : R (f a),
      { dsimp [R],
        rw presieve.mem_of_arrows_iff,
        use [a, rfl],
        simp },
      rw hh (f a) this,
      dsimp [y],
      specialize compat (aa (f a) this) a (X a) (eq_to_hom _) (𝟙 _) _,
      { apply haa },
      rw category.id_comp,
      apply (haa' _ _).symm,
      simpa using compat } }
end

theorem is_proetale_sheaf_of_types_pullback_iff :
  P.is_proetale_sheaf_of_types ↔ P.is_proetale_sheaf_of_types_pullback :=
begin
  split,
  { introsI h α _ B X f surj x compat,
    apply h α B X f surj x,
    intros a b Z g₁ g₂ h,
    let g : Z ⟶ limits.pullback (f a) (f b) := limits.pullback.lift _ _ h,
    rw (show g₁ = g ≫ limits.pullback.fst, by simp [g]),
    rw (show g₂ = g ≫ limits.pullback.snd, by simp [g]),
    simp only [op_comp, P.map_comp],
    dsimp,
    rw compat },
  { introsI h α _ B X f surj x compat,
    apply h α B X f surj x,
    intros a b,
    apply compat,
    exact limits.pullback.condition }
end

theorem is_proetale_sheaf_of_types_explicit_pullback_iff :
  P.is_proetale_sheaf_of_types ↔ P.is_proetale_sheaf_of_types_explicit_pullback :=
begin
  split,
  { introsI h α _ B X f surj x compat,
    apply h α B X f surj x,
    intros a b Z g₁ g₂ h,
    let g : Z ⟶ Profinite.pullback (f a) (f b) := Profinite.pullback.lift (f a) (f b) g₁ g₂ h,
    rw (show g₁ = g ≫ Profinite.pullback.fst (f a) (f b), by simp [g]),
    rw (show g₂ = g ≫ Profinite.pullback.snd (f a) (f b), by simp [g]),
    simp only [op_comp, P.map_comp],
    dsimp,
    rw compat },
  { introsI h α _ B X f surj x compat,
    apply h α B X f surj x,
    intros a b,
    apply compat,
    exact Profinite.pullback.condition _ _ }
end

theorem equalizer_condition_of_is_proetale_sheaf_of_types
  (h : P.is_proetale_sheaf_of_types) : P.equalizer_condition :=
begin
  intros X B π surj,
  rw is_proetale_sheaf_of_types_explicit_pullback_iff at h,
  specialize h punit B (λ _, X) (λ _, π) _,
  { intros b,
    use punit.star,
    apply surj },
  dsimp at h,
  split,
  { intros x y hh,
    dsimp [map_to_equalizer] at hh,
    apply_fun (λ e, e.val) at hh,
    specialize h (λ _, P.map π.op x) _,
    { intros,
      dsimp,
      change (P.map _ ≫ P.map _) _ = (P.map _ ≫ P.map _) _,
      simp_rw [← P.map_comp, ← op_comp, Profinite.pullback.condition] },
    obtain ⟨t,ht1,ht2⟩ := h,
    have hx : x = t,
    { apply ht2,
      intros,
      refl },
    have hy : y = t,
    { apply ht2,
      intros a,
      exact hh.symm },
    rw [hx, ← hy] },
  { rintros ⟨x,hx⟩,
    specialize h (λ _, x) _,
    { intros,
      exact hx },
    obtain ⟨t,ht1,ht2⟩ := h,
    use [t],
    ext1,
    exact ht1 punit.star }
end

noncomputable theory

def sigma_pi_equiv {α : Fintype.{w}} (X : α → Profinite.{w}) (h : P.finite_product_condition) :
  P.obj (op $ Profinite.sigma X) ≃ Π a, P.obj (op $ X a) :=
equiv.of_bijective _ (h α X)

def equalizer_equiv {S₁ S₂ : Profinite}
  (h : P.equalizer_condition) (f : S₁ ⟶ S₂) (surj : function.surjective f) :
  P.obj (op S₂) ≃ { x : P.obj (op S₁) |
    P.map (Profinite.pullback.fst f f).op x = P.map (Profinite.pullback.snd f f).op x } :=
equiv.of_bijective _ (h _ _ _ surj)

lemma equalizes_of_compat {α : Fintype.{w}} {B} {X : α → Profinite.{w}}
  (h : P.finite_product_condition) (f : Π a, X a ⟶ B) (x : Π a, P.obj (op $ X a))
  (compat : ∀ a b, P.map (Profinite.pullback.fst (f a) (f b)).op (x a) =
    P.map (Profinite.pullback.snd (f a) (f b)).op (x b)) :
  P.map (Profinite.pullback.fst (Profinite.sigma.desc X f) (Profinite.sigma.desc X f)).op
    ((sigma_pi_equiv P X h).symm x) =
  P.map (Profinite.pullback.snd (Profinite.sigma.desc X f) (Profinite.sigma.desc X f)).op
    ((sigma_pi_equiv P X h).symm x) :=
begin
  let I := Profinite.sigma_pullback_to_pullback_sigma X f,
  apply_fun P.map I.op,
  swap, {
    intros i j hh,
    apply_fun P.map (category_theory.inv I).op at hh,
    change (P.map _ ≫ P.map _) _ = (P.map _ ≫ P.map _) _ at hh,
    simp_rw [← P.map_comp, ← op_comp] at hh,
    simpa using hh },
  change (P.map _ ≫ P.map _) _ = (P.map _ ≫ P.map _) _,
  simp_rw [← P.map_comp, ← op_comp],
  erw Profinite.sigma_pullback_to_pullback_sigma_fst,
  erw Profinite.sigma_pullback_to_pullback_sigma_snd,
  let E := sigma_pi_equiv P X h,
  specialize h ⟨α × α⟩ (λ a, Profinite.pullback (f a.1) (f a.2)),
  let E' := equiv.of_bijective _ h,
  apply_fun E',
  ext1 ⟨a,b⟩,
  dsimp [E'],
  change (P.map _ ≫ P.map _) _ = (P.map _ ≫ P.map _) _,
  simp_rw [← P.map_comp, ← op_comp, Profinite.sigma.ι_desc],
  dsimp,
  simp_rw [P.map_comp],
  convert compat a b,
  all_goals { dsimp [coe_comp],
    congr' 1,
    change ((E ∘ E.symm) x) _ = _,
    simp },
end

theorem is_proetale_sheaf_of_finite_product_condition_of_equalizer_condition
  (h1 : P.finite_product_condition) (h2 : P.equalizer_condition) :
  P.is_proetale_sheaf_of_types :=
begin
  rw is_proetale_sheaf_of_types_explicit_pullback_iff,
  introsI α _ B X f surj x compat,
  let A : Fintype := Fintype.of α,
  change Π (x : A), _ at x,
  change Π (x : A), _ at f,
  change ∀ (a b : A), _ at compat,
  change A → _ at X,
  let E := sigma_pi_equiv P X h1,
  let F := equalizer_equiv P h2 (Profinite.sigma.desc X f)
    (Profinite.sigma.desc_surjective _ _ surj),
  let π1 := Profinite.pullback.fst (Profinite.sigma.desc X f) (Profinite.sigma.desc X f),
  let π2 := Profinite.pullback.snd (Profinite.sigma.desc X f) (Profinite.sigma.desc X f),
  let S := P.obj (op $ Profinite.sigma X),
  let x' : { t : S | P.map π1.op t = P.map π2.op t } := ⟨E.symm x, _⟩,
  swap, { exact equalizes_of_compat P h1 f x compat },
  use F.symm x',
  split,
  { dsimp,
    intros a,
    have : P.map (f a).op = ((λ u : Π a, P.obj (op $ X a), u a) ∘
      (λ u : { t : S | P.map π1.op t = P.map π2.op t }, E u.val) ∘ F),
    { ext t, dsimp [E, F, sigma_pi_equiv, equalizer_equiv, map_to_equalizer],
      change _ = (P.map _ ≫ P.map _) _,
      simp_rw [← P.map_comp, ← op_comp, Profinite.sigma.ι_desc] },
    rw this,
    change ((λ u : Π a, P.obj (op $ X a), u a) ∘
      (λ u : { t : S | P.map π1.op t = P.map π2.op t }, E u.val) ∘ F ∘ F.symm) x' = _,
    simp },
  { intros y hy,
    apply_fun F,
    change _ = (F ∘ F.symm) x',
    simp only [equiv.self_comp_symm, id.def],
    ext1,
    apply_fun E,
    change _ = (E ∘ E.symm) _,
    simp only [equiv.self_comp_symm, id.def],
    dsimp [E,F, sigma_pi_equiv, equalizer_equiv, map_to_equalizer],
    ext a,
    change (P.map _ ≫ P.map _) _ = _,
    simp_rw [← P.map_comp, ← op_comp, Profinite.sigma.ι_desc, hy a] }
end

theorem is_proetale_sheaf_of_types_tfae :
  [ presieve.is_sheaf proetale_topology P
  , P.is_proetale_sheaf_of_types
  , P.is_proetale_sheaf_of_types_pullback
  , P.is_proetale_sheaf_of_types_explicit_pullback
  , P.finite_product_condition ∧ P.equalizer_condition
  , P.empty_condition ∧ P.product_condition ∧ P.equalizer_condition
  ].tfae :=
begin
  tfae_have : 1 ↔ 2, { exact P.is_proetale_sheaf_of_types_iff.symm },
  tfae_have : 2 ↔ 3, { exact P.is_proetale_sheaf_of_types_pullback_iff },
  tfae_have : 2 ↔ 4, { exact P.is_proetale_sheaf_of_types_explicit_pullback_iff },
  tfae_have : 2 → 5, {
    intros h,
    split,
    { exact finite_product_condition_of_is_proetale_sheaf_of_types _ h },
    { exact equalizer_condition_of_is_proetale_sheaf_of_types _ h } },
  tfae_have : 5 → 2, {
    rintros ⟨h1,h2⟩,
    apply is_proetale_sheaf_of_finite_product_condition_of_equalizer_condition,
    assumption' },
  tfae_have : 5 ↔ 6, {
    rw finite_product_condition_iff_empty_condition_product_condition,
    rw and_assoc },
  tfae_finish
end

def is_proetale_sheaf : Prop := ∀
-- a finite family of morphisms with base B
(α : Type w) [fintype α] (B : Profinite.{w}) (X : α → Profinite.{w}) (f : Π a, X a ⟶ B)
-- jointly surjective
(surj : ∀ b : B, ∃ a (x : X a), f a x = b)
-- test object
(T : C)
-- family of moprhisms
(x : Π a, T ⟶ Q.obj (op (X a)))
-- which is compatible
(compat : ∀ (a b : α) (Z : Profinite.{w}) (g₁ : Z ⟶ X a) (g₂ : Z ⟶ X b),
  (g₁ ≫ f a = g₂ ≫ f b) → x a ≫ Q.map g₁.op = x b ≫ Q.map g₂.op),
-- the actual condition
∃! t : T ⟶ Q.obj (op B), ∀ a : α, t ≫ Q.map (f a).op = x a

def is_proetale_sheaf_pullback : Prop := ∀
-- a finite family of morphisms with base B
(α : Type w) [fintype α] (B : Profinite.{w}) (X : α → Profinite.{w}) (f : Π a, X a ⟶ B)
-- jointly surjective
(surj : ∀ b : B, ∃ a (x : X a), f a x = b)
-- test object
(T : C)
-- family of moprhisms
(x : Π a, T ⟶ Q.obj (op (X a)))
-- which is compatible
(compat : ∀ (a b : α), x a ≫ Q.map (limits.pullback.fst : limits.pullback (f a) (f b) ⟶ _).op =
  x b ≫ Q.map limits.pullback.snd.op),
-- the actual condition
∃! t : T ⟶ Q.obj (op B), ∀ a : α, t ≫ Q.map (f a).op = x a

theorem is_proetale_sheaf_pullback_iff : Q.is_proetale_sheaf ↔ Q.is_proetale_sheaf_pullback :=
begin
  split,
  { introsI h α _ B X f surj T x compat,
    apply h α B X f surj T x,
    intros a b Z g₁ g₂ h,
    specialize compat a b,
    let g : Z ⟶ limits.pullback (f a) (f b) := limits.pullback.lift g₁ g₂ h,
    rw (show g₁ = g ≫ limits.pullback.fst, by simp [g]),
    rw (show g₂ = g ≫ limits.pullback.snd, by simp [g]),
    simp only [op_comp, Q.map_comp, reassoc_of compat] },
  { introsI h α _ B X f surj T x compat,
    apply h α B X f surj T x,
    intros a b,
    apply compat,
    exact limits.pullback.condition }
end

theorem is_proetale_sheaf_iff : Q.is_proetale_sheaf ↔ presheaf.is_sheaf proetale_topology Q :=
begin
  split,
  { intros h T,
    rw ← (Q ⋙ coyoneda.obj (op T)).is_proetale_sheaf_of_types_iff,
    introsI α _ B X f surj x compat,
    exact h α B X f surj T x compat },
  { introsI h α _ B X f surj T x compat,
    specialize h T,
    rw ← (Q ⋙ coyoneda.obj (op T)).is_proetale_sheaf_of_types_iff at h,
    exact h α B X f surj x compat }
end

def empty_condition' [limits.has_terminal C] : Prop :=
  is_iso (limits.terminal.from (Q.obj (op Profinite.empty)))

def product_condition' [limits.has_binary_products C] : Prop := ∀ (X Y : Profinite.{w}),
  is_iso (limits.prod.lift (Q.map (Profinite.sum.inl X Y).op) (Q.map (Profinite.sum.inr X Y).op))

def map_to_equalizer' [limits.has_equalizers C] {X Y Z : Profinite.{w}} (f : Y ⟶ X)
  (g₁ g₂ : Z ⟶ Y) (w : g₁ ≫ f = g₂ ≫ f) : Q.obj (op X) ⟶
  limits.equalizer (Q.map g₁.op) (Q.map g₂.op) :=
limits.equalizer.lift (Q.map f.op) begin
  simp only [← Q.map_comp, ← op_comp, w]
end

def equalizer_condition' [limits.has_equalizers C] : Prop := ∀ (X Y : Profinite.{w})
  (f : X ⟶ Y) (hf : function.surjective f),
  is_iso (Q.map_to_equalizer' f (Profinite.pullback.fst f f) (Profinite.pullback.snd f f)
    (Profinite.pullback.condition _ _))

lemma empty_of_empty_coyoneda [limits.has_terminal C] :
  (∀ X : C, (Q ⋙ coyoneda.obj (op X)).empty_condition) → Q.empty_condition' :=
begin
  intro h,
  have hh := h (⊤_ C),
  have hh' := h (Q.obj (op $ Profinite.empty)),
  let P := Q ⋙ coyoneda.obj (op $ Q.obj (op $ Profinite.empty)),
  rcases hh with ⟨h1,h2⟩,
  rcases hh' with ⟨h1',h2'⟩,
  dsimp [empty_condition'],
  obtain ⟨f,-⟩ := h2 punit.star,
  use f,
  simp only [and_true, eq_iff_true_of_subsingleton],
  apply h1',
  simp
end

lemma empty_coyoneda_of_empty [limits.has_terminal C] :
  Q.empty_condition' → (∀ X : C, (Q ⋙ coyoneda.obj (op X)).empty_condition) :=
begin
  intros h X,
  let e := limits.terminal.from (Q.obj (op $ Profinite.empty)),
  change is_iso e at h,
  resetI,
  split,
  { rintros f g -,
    dsimp [coyoneda, empty_condition'] at f g,
    suffices : f ≫ e = g ≫ e, {
      apply_fun (λ t, t ≫ category_theory.inv e) at this,
      simp_rw [category.assoc] at this,
      simpa only [category.comp_id, is_iso.hom_inv_id] using this },
    simp only [eq_iff_true_of_subsingleton] },
  { rintros a,
    dsimp [coyoneda],
    use limits.terminal.from X ≫ category_theory.inv e,
    simp }
end

lemma product_of_product_coyoneda [limits.has_binary_products C] :
  (∀ X : C, (Q ⋙ coyoneda.obj (op X)).product_condition) → Q.product_condition' :=
begin
  intro h,
  intros X Y,
  have hh := h (Q.obj (op X) ⨯ Q.obj (op Y)),
  have hh' := h (Q.obj (op $ Profinite.sum X Y)),
  let P1 := Q ⋙ coyoneda.obj (op $ Q.obj (op X) ⨯ Q.obj (op Y)),
  let P2 := Q ⋙ coyoneda.obj (op $ Q.obj (op $ Profinite.sum X Y)),
  specialize hh X Y,
  specialize hh' X Y,
  dsimp [P1,P2, coyoneda] at hh hh',
  rcases hh with ⟨-,hh⟩,
  rcases hh' with ⟨hh',-⟩,
  obtain ⟨f,hf⟩ := hh ⟨limits.prod.fst, limits.prod.snd⟩,
  use f,
  dsimp at *,
  simp only [prod.mk.inj_iff] at hf,
  cases hf with hf1 hf2,
  simp only [hf1, hf2, and_true, limits.prod.comp_lift,
    limits.prod.lift_fst_snd, eq_self_iff_true],
  apply hh',
  simp [hf1,hf2]
end

lemma product_coyoneda_of_product [limits.has_binary_products C] :
  Q.product_condition' → (∀ X : C, (Q ⋙ coyoneda.obj (op X)).product_condition) :=
begin
  intros h X A B,
  specialize h A B,
  let e := limits.prod.lift (Q.map (Profinite.sum.inl A B).op) (Q.map (Profinite.sum.inr A B).op),
  change is_iso e at h,
  resetI,
  split,
  { intros f g hh,
    dsimp at f g hh,
    simp only [prod.mk.inj_iff] at hh,
    rcases hh with ⟨hl,hr⟩,
    suffices : f ≫ e = g ≫ e,
    { apply_fun (λ t, t ≫ category_theory.inv e) at this,
      simp_rw category.assoc at this,
      simpa using this },
    apply limits.prod.hom_ext,
    { simp [hl] },
    { simp [hr] } },
  { rintros ⟨a,b⟩,
    dsimp at a b ⊢,
    use limits.prod.lift a b ≫ category_theory.inv e,
    have ha : category_theory.inv e ≫ Q.map (Profinite.sum.inl A B).op = limits.prod.fst,
    { simp [is_iso.inv_comp_eq,e] },
    have hb : category_theory.inv e ≫ Q.map (Profinite.sum.inr A B).op = limits.prod.snd,
    { simp [is_iso.inv_comp_eq,e] },
    simp [ha,hb] }
end

lemma equalizer_of_equalizer_coyoneda [limits.has_equalizers C] :
  (∀ X : C, (Q ⋙ coyoneda.obj (op X)).equalizer_condition) → Q.equalizer_condition' :=
begin
  intros h X B f hf,
  let h1 := h (Q.obj (opposite.op B)) X B f hf,
  let π1 := Profinite.pullback.fst f f,
  let π2 := Profinite.pullback.snd f f,
  let h2 := h (limits.equalizer (Q.map π1.op) (Q.map π2.op)) X B f hf,
  dsimp [map_to_equalizer] at h1 h2,
  obtain ⟨e,he⟩ := h2.2 ⟨limits.equalizer.ι _ _, _⟩,
  swap, { dsimp [π1,π2], simp [limits.equalizer.condition] },
  use e,
  dsimp [map_to_equalizer'] at *,
  simp at he,
  split,
  { apply h1.1,
    simp [he] },
  { apply limits.equalizer.hom_ext, simp [he], }
end

lemma equalizer_coyoneda_of_equalizer [limits.has_equalizers C] :
  Q.equalizer_condition' → (∀ X : C, (Q ⋙ coyoneda.obj (op X)).equalizer_condition) :=
begin
  intros h X A B f hf,
  specialize h A B f hf,
  let e := Q.map_to_equalizer' f (Profinite.pullback.fst f f) (Profinite.pullback.snd f f)
    (Profinite.pullback.condition _ _),
  change is_iso e at h,
  resetI,
  split,
  { intros a b hh,
    dsimp [map_to_equalizer] at a b hh,
    simp at hh,
    suffices : a ≫ e = b ≫ e, {
      apply_fun (λ t, t ≫ category_theory.inv e) at this,
      simp_rw [category.assoc] at this,
      simpa using this },
    apply limits.equalizer.hom_ext,
    simpa [e, map_to_equalizer'] },
  { rintros ⟨a,ha⟩,
    dsimp at a ha,
    use limits.equalizer.lift a ha ≫ category_theory.inv e,
    have : category_theory.inv e ≫ Q.map f.op = limits.equalizer.ι _ _,
    { simp [e,is_iso.comp_inv_eq, map_to_equalizer'] },
    simp [map_to_equalizer, this] }
end

theorem is_proetale_sheaf_of_empty_of_product_of_equalizer
  [limits.has_terminal C] [limits.has_binary_products C] [limits.has_equalizers C] :
  Q.empty_condition' ∧ Q.product_condition' ∧ Q.equalizer_condition' → Q.is_proetale_sheaf :=
begin
  rintro ⟨h1,h2,h3⟩,
  rw is_proetale_sheaf_iff,
  intros X,
  rw (Q ⋙ coyoneda.obj (op X)).is_proetale_sheaf_of_types_tfae.out 0 5,
  refine ⟨_,_,_⟩,
  { apply empty_coyoneda_of_empty, exact h1 },
  { apply product_coyoneda_of_product, exact h2 },
  { apply equalizer_coyoneda_of_equalizer, exact h3 }
end

theorem is_proetale_sheaf_tfae [limits.has_terminal C] [limits.has_binary_products C]
  [limits.has_equalizers C] :
  [ presheaf.is_sheaf proetale_topology Q,
    Q.is_proetale_sheaf,
    Q.is_proetale_sheaf_pullback,
    Q.empty_condition' ∧ Q.product_condition' ∧ Q.equalizer_condition'
  ].tfae :=
begin
  tfae_have : 1 ↔ 2, { exact Q.is_proetale_sheaf_iff.symm },
  tfae_have : 2 ↔ 3, { exact Q.is_proetale_sheaf_pullback_iff },
  tfae_have : 1 → 4,
  { intros h,
    refine ⟨_,_,_⟩,
    { apply empty_of_empty_coyoneda,
      intros X,
      specialize h X,
      rw (Q ⋙ coyoneda.obj (op X)).is_proetale_sheaf_of_types_tfae.out 0 5 at h,
      exact h.1 },
    { apply product_of_product_coyoneda,
      intros X,
      specialize h X,
      rw (Q ⋙ coyoneda.obj (op X)).is_proetale_sheaf_of_types_tfae.out 0 5 at h,
      exact h.2.1 },
    { apply equalizer_of_equalizer_coyoneda,
      intros X,
      specialize h X,
      rw (Q ⋙ coyoneda.obj (op X)).is_proetale_sheaf_of_types_tfae.out 0 5 at h,
      exact h.2.2 } },
  tfae_have : 4 → 1,
  { intros h X,
    rw (Q ⋙ coyoneda.obj (op X)).is_proetale_sheaf_of_types_tfae.out 0 5,
    refine ⟨_,_,_⟩,
    { apply empty_coyoneda_of_empty, exact h.1 },
    { apply product_coyoneda_of_product, exact h.2.1 },
    { apply equalizer_coyoneda_of_equalizer, exact h.2.2 } },
  tfae_finish
end

end category_theory.functor
