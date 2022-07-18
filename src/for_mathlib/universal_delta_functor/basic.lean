import category_theory.abelian.basic
import category_theory.preadditive.additive_functor
import for_mathlib.short_exact_sequence

noncomputable theory

namespace category_theory

universes v v' u u'
variables (A : Type u) (B : Type u')
  [category.{v} A] [category.{v} B] [abelian A] [abelian B]

/-- Cohomological covariant delta functor. -/
@[nolint has_inhabited_instance]
structure delta_functor :=
(F : ℕ → A ⥤ B)
[additive : ∀ n, functor.additive (F n)]
(δ : Π (n : ℕ),
  short_exact_sequence.Trd A ⋙ (F n) ⟶ short_exact_sequence.Fst A ⋙ (F (n+1)))
(mono : ∀ (S : short_exact_sequence _), mono ((F 0).map S.f))
(exact' : ∀ (n : ℕ) (S : short_exact_sequence _), exact ((F n).map S.f) ((F n).map S.g))
(exact_δ : ∀ (n : ℕ) (S : short_exact_sequence _),
  exact ((F n).map S.g) ((δ n).app S))
(δ_exact : ∀ (n : ℕ) (S : short_exact_sequence _),
  exact ((δ n).app S) ((F (n+1)).map S.f))

namespace delta_functor

infixr ` ⥤δ `:26 := delta_functor

instance : has_coe_to_fun (A ⥤δ B) (λ F, ℕ → (A ⥤ B)) := ⟨F⟩

variables {A B}

/-- Morphisms of cohomological covariant delta functors. -/
@[nolint has_inhabited_instance]
structure hom (F G : A ⥤δ B) :=
(η : Π n, F n ⟶ G n)
(comm' : ∀ n, F.δ n ≫ whisker_left _ (η _) = whisker_left _ (η _) ≫ G.δ _)

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
lemma comm {F G : A ⥤δ B} (η : F ⟶ G) (n : ℕ) (S : short_exact_sequence A) :
  (F.δ n).app S ≫ (η (n+1)).app S.fst =
  (η n).app S.trd ≫ (G.δ n).app S :=
begin
  have := η.comm' n,
  apply_fun (λ e, e.app S) at this,
  exact this,
end

/-- Identity morphisms of delta functors. -/
def id (F : A ⥤δ B) : F ⟶ F :=
⟨λ n, 𝟙 _, begin
  intros n,
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
    intros n, ext,
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

namespace stacks_010T

structure effacement (F : A ⥤δ B) (X : A) (n : ℕ) :=
(I : A)
(ι : X ⟶ I)
[mono : category_theory.mono ι]
(w : (F (n+1)).map ι = 0)

instance effacement_mono (F : A ⥤δ B) (X : A) (n : ℕ)
  (e : effacement F X n) : category_theory.mono e.ι := e.mono

class effacable (F : A ⥤δ B) : Prop :=
(cond [] : ∀ (X : A) (n : ℕ), nonempty (effacement F X n))

def choose_effacement (F : A ⥤δ B) [effacable F] (X : A) (n : ℕ) : effacement F X n :=
(effacable.cond F X n).some

def effacement.ses {F : A ⥤δ B} {X n} (e : effacement F X n) : short_exact_sequence A :=
{ fst := X,
  snd := e.I,
  trd := limits.cokernel e.ι,
  f := e.ι,
  g := limits.cokernel.π _,
  exact' := abelian.exact_cokernel e.ι }

def effacement.cokernel_comparison {F : A ⥤δ B} {X n} (e : effacement F X n) :
  limits.cokernel ((F n).map (limits.cokernel.π e.ι)) ⟶ (F (n+1)).obj X :=
limits.cokernel.desc _ ((F.δ n).app e.ses) (F.exact_δ n e.ses).w

instance effacement.epi_cokernel_comparison {F : A ⥤δ B} {X n} (e : effacement F X n) :
  epi e.cokernel_comparison := sorry

instance effacement.mono_cokernel_comparison {F : A ⥤δ B} {X n} (e : effacement F X n) :
  category_theory.mono e.cokernel_comparison := sorry

instance effacement.is_iso_cokernel_comparison {F : A ⥤δ B} {X n} (e : effacement F X n) :
  is_iso e.cokernel_comparison :=
is_iso_of_mono_of_epi _

def effacement.cokernel_iso {F : A ⥤δ B} {X n} (e : effacement F X n) :
  limits.cokernel ((F n).map (limits.cokernel.π e.ι)) ≅ (F (n+1)).obj X :=
as_iso e.cokernel_comparison

@[simp, reassoc]
lemma cokernel_iso_spec {F : A ⥤δ B} {X n} (e : effacement F X n) :
  limits.cokernel.π _ ≫ e.cokernel_iso.hom =
  (F.δ n).app e.ses :=
limits.cokernel.π_desc _ _ _

end stacks_010T

-- Sketch:
-- TODO: Prove stacks tag 010T.
-- TODO: Construct `Ext^*(-,X)` a delta functor (on objects!).
-- These should be functors `Aᵒᵖ ⥤ Ab` (assuming `A` has enough projectives).
-- Use `010T` to see that `Ext^*(-,X)` is universal.

end delta_functor

end category_theory
