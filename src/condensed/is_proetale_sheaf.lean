import condensed.proetale_site
import for_mathlib.presieve
import topology.category.Profinite.projective
import for_mathlib.Profinite.disjoint_union

universes w v u

namespace category_theory.functor

open category_theory opposite

variables {C : Type u} [category.{v} C] (Q : Profinite.{w}ᵒᵖ ⥤ C)
variables (P : Profinite.{w}ᵒᵖ ⥤ Type u)

def finite_product_condition : Prop := ∀
(α : Fintype.{w}) (X : α → Profinite.{w}),
function.bijective (λ (x : P.obj (op (Profinite.sigma X))) (a : α),
  P.map (Profinite.sigma.ι X a).op x)

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

theorem is_prroetale_sheaf_pullback_iff : Q.is_proetale_sheaf ↔ Q.is_proetale_sheaf_pullback :=
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

end category_theory.functor
