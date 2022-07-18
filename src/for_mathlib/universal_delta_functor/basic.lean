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

class preuniversal (F : A ⥤δ B) : Prop :=
(cond [] : ∀ (X : A) (n : ℕ), ∃ (I : A) (f : X ⟶ I) (hf : category_theory.mono f),
  (F (n+1)).map f = 0)

variables (F : A ⥤δ B) [preuniversal F]

def hull (X : A) (n : ℕ) : A :=
(preuniversal.cond F X n).some

def ι (X : A) (n : ℕ) : X ⟶ hull F X n :=
(preuniversal.cond F X n).some_spec.some

instance mono_ι (X : A) (n : ℕ) : category_theory.mono (ι F X n) :=
(preuniversal.cond F X n).some_spec.some_spec.some

def ι_spec (X : A) (n : ℕ) : (F (n+1)).map (ι F X n) = 0 :=
(preuniversal.cond F X n).some_spec.some_spec.some_spec

def ses (X : A) (n : ℕ) : short_exact_sequence A :=
{ fst := X,
  snd := hull F X n,
  trd := limits.cokernel (ι F X n),
  f := ι F X n,
  g := limits.cokernel.π _,
  exact' := abelian.exact_cokernel (ι F X n) }

def cokernel_comparison (X : A) (n : ℕ) :
  limits.cokernel ((F n).map (limits.cokernel.π (ι F X n))) ⟶ (F (n+1)).obj X :=
limits.cokernel.desc _ ((F.δ n).app $ ses F X n) (F.exact_δ n (ses F X n)).w

instance epi_cokernel_comparison (X : A) (n : ℕ) :
  epi (cokernel_comparison F X n) := sorry

instance mono_cokernel_comparison (X : A) (n : ℕ) :
  category_theory.mono (cokernel_comparison F X n) := sorry

instance is_iso_cokernel_comparison (X : A) (n : ℕ) :
  is_iso (cokernel_comparison F X n) :=
is_iso_of_mono_of_epi _

def cokernel_iso (X : A) (n : ℕ) :
  limits.cokernel ((F n).map (limits.cokernel.π (ι F X n))) ≅ (F (n+1)).obj X :=
as_iso (cokernel_comparison F X n)

@[simp, reassoc]
lemma cokernel_iso_spec (X : A) (n : ℕ) :
  limits.cokernel.π _ ≫ (cokernel_iso F X n).hom =
  (F.δ n).app (ses F X n) :=
limits.cokernel.π_desc _ _ _

end stacks_010T

-- Sketch:
-- TODO: Prove stacks tag 010T.
-- TODO: Construct `Ext^*(-,X)` a delta functor (on objects!).
-- These should be functors `Aᵒᵖ ⥤ Ab` (assuming `A` has enough projectives).
-- Use `010T` to see that `Ext^*(-,X)` is universal.

end delta_functor

end category_theory
