import condensed.proetale_site
import for_mathlib.presieve
import topology.category.Profinite.projective
import for_mathlib.Profinite.disjoint_union

universes w v u

namespace category_theory.functor

open category_theory opposite

variables {C : Type u} [category.{v} C] (Q : Profinite.{w}ᵒᵖ ⥤ C)
variables (P : Profinite.{w}ᵒᵖ ⥤ Type u)

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

def is_proetale_sheaf_of_types_projective : Prop := ∀
-- a finite family of projective objects
(α : Fintype.{w}) (X : α → Profinite.{w}) [∀ a, projective (X a)],
function.bijective (λ (x : P.obj (op $ Profinite.sigma X)) (a : α),
  P.map (Profinite.sigma.ι _ a).op x)

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
