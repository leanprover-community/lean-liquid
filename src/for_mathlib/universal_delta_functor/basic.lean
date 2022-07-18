import category_theory.abelian.basic
import category_theory.preadditive.additive_functor
import for_mathlib.short_exact_sequence

namespace category_theory

universes v v' u u'
variables (A : Type u) (B : Type u')
  [category.{v} A] [category.{v} B] [abelian A] [abelian B]

/-- Cohomological covariant delta functor. -/
@[nolint has_inhabited_instance]
structure delta_functor :=
(F : ℕ → A ⥤ B)
[additive : ∀ n, functor.additive (F n)]
(δ : Π (m n : ℕ) (h : n = m+1),
  short_exact_sequence.Trd A ⋙ (F m) ⟶ short_exact_sequence.Fst A ⋙ (F n))
(mono : ∀ (S : short_exact_sequence _), mono ((F 0).map S.f))
(exact' : ∀ (n : ℕ) (S : short_exact_sequence _), exact ((F n).map S.f) ((F n).map S.g))
(exact_δ : ∀ (m n : ℕ) (h : n = m+1) (S : short_exact_sequence _),
  exact ((F m).map S.g) ((δ m n h).app S))
(δ_exact : ∀ (m n : ℕ) (h : n = m+1) (S : short_exact_sequence _),
  exact ((δ m n h).app S) ((F n).map S.f))

namespace delta_functor

infixr ` ⥤δ `:26 := delta_functor

instance : has_coe_to_fun (A ⥤δ B) (λ F, ℕ → (A ⥤ B)) := ⟨F⟩

variables {A B}

/-- Morphisms of cohomological covariant delta functors. -/
@[nolint has_inhabited_instance]
structure hom (F G : A ⥤δ B) :=
(η : Π n, F n ⟶ G n)
(comm' : ∀ m n h, F.δ m n h ≫ whisker_left _ (η _) = whisker_left _ (η _) ≫ G.δ _ _ h)

instance : quiver (A ⥤δ B) :=
{ hom := hom }

namespace hom

instance {F G : A ⥤δ B} : has_coe_to_fun (F ⟶ G) (λ η, Π n, F n ⟶ G n) :=
⟨η⟩

@[ext]
lemma ext {F G : A ⥤δ B} (η γ : F ⟶ G) (h : ∀ n, η n = γ n) : η = γ :=
by { cases η, cases γ, congr, ext1, apply h }

@[simp]
lemma η_eq_coe {F G : A ⥤δ B} (η : F ⟶ G) (n : ℕ) :
  η.η n = η n := rfl

@[simp, reassoc]
lemma comm {F G : A ⥤δ B} (η : F ⟶ G) (m n : ℕ) (h : n = m+1) (S : short_exact_sequence A) :
  (F.δ m n h).app S ≫ (η n).app S.fst =
  (η m).app S.trd ≫ (G.δ m n h).app S :=
begin
  have := η.comm' m n h,
  apply_fun (λ e, e.app S) at this,
  exact this,
end

/-- Identity morphisms of delta functors. -/
def id (F : A ⥤δ B) : F ⟶ F :=
⟨λ n, 𝟙 _, begin
  rintros m n ⟨rfl⟩,
  ext, dsimp,
  erw nat_trans.id_app,
  erw nat_trans.id_app,
  simp,
end⟩

@[simp]
lemma id_apply (F : A ⥤δ B) (n : ℕ) :
  id F n = 𝟙 _ := rfl

/-- Compositions of morphisms of delta functors. -/
def comp {F G H : A ⥤δ B} (η : F ⟶ G) (γ : G ⟶ H) :
  hom F H :=
{ η := λ n, η n ≫ γ n,
  comm' := begin
    rintros m n rfl, ext,
    dsimp,
    simp,
  end }

@[simp]
lemma comp_apply {F G H : A ⥤δ B} (η : F ⟶ G) (γ : G ⟶ H) (n : ℕ) :
  (hom.comp η γ) n = η n ≫ γ n := rfl

end hom

/-- delta functors form a category. -/
instance category : category (A ⥤δ B) :=
{ id := λ F, hom.id _,
  comp := λ X Y Z F G, hom.comp F G,
  id_comp' := by { intros F G f, ext, dsimp, simp },
  comp_id' := by { intros F G f, ext, dsimp, simp },
  assoc' := by { intros F G H W a b c, ext, dsimp, simp },
  ..(infer_instance : quiver (A ⥤δ B)) }

/-- Universal delta functors. -/
class universal (F : A ⥤δ B) : Prop :=
(cond : ∀ (G : A ⥤δ B) (e0 : F 0 ⟶ G 0), ∃! e : F ⟶ G, (e : Π n, F n ⟶ G n) 0 = e0)

-- Sketch:
-- TODO: Prove stacks tag 010T.
-- TODO: Construct `Ext^*(-,X)` a delta functor (on objects!).
-- These should be functors `Aᵒᵖ ⥤ Ab` (assuming `A` has enough projectives).
-- Use `010T` to see that `Ext^*(-,X)` is universal.

end delta_functor

end category_theory
