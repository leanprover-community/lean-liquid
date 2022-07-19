import category_theory.abelian.basic
import category_theory.preadditive.additive_functor
import for_mathlib.short_exact_sequence
import for_mathlib.abelian_category
import for_mathlib.exact_lift_desc

/-!

Refs:
1. Grothendieck's Tôhoku paper
2. Stacks tag 010T

-/

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

instance additive_apply (F : A ⥤δ B) (n : ℕ) :
  functor.additive (F n) := F.additive n

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

namespace tohoku

/-- An effacement relative to a δ functor. -/
@[nolint has_inhabited_instance]
structure effacement (F : A ⥤δ B) (X : A) (n : ℕ) :=
(I : A)
(ι : X ⟶ I)
[mono : category_theory.mono ι]
(w : (F (n+1)).map ι = 0)

/-- Morphisms between effacements. -/
@[ext, nolint has_inhabited_instance]
structure effacement.hom (F : A ⥤δ B) (X : A) (n : ℕ)
  (e₁ e₂ : effacement F X n) :=
(t : e₁.I ⟶ e₂.I)
(w : e₁.ι ≫ t = e₂.ι)

instance effacement.category (F : A ⥤δ B) (X : A) (n : ℕ) :
  category (effacement F X n) :=
{ hom := λ e₁ e₂, e₁.hom _ _ _ e₂,
  id := λ e, ⟨𝟙 _, category.comp_id _⟩,
  comp := λ a b c f g, ⟨f.t ≫ g.t, by simp [reassoc_of f.w, g.w]⟩,
  id_comp' := λ a b f, effacement.hom.ext _ _ $ category.id_comp _,
  comp_id' := λ a b f, effacement.hom.ext _ _ $ category.comp_id _,
  assoc' := λ a b c d f g h,
    effacement.hom.ext _ _ $ category.assoc _ _ _ }

instance effacement_mono (F : A ⥤δ B) (X : A) (n : ℕ)
  (e : effacement F X n) : category_theory.mono e.ι := e.mono

/-- Effacable δ functors. -/
class effacable (F : A ⥤δ B) : Prop :=
(cond [] : ∀ (X : A) (n : ℕ), nonempty (effacement F X n))

/-- A choice of effacement. -/
def choose_effacement (F : A ⥤δ B) [effacable F] (X : A) (n : ℕ) : effacement F X n :=
(effacable.cond F X n).some

/-- A short exact sequence associated to an effacement -/
def effacement.ses {F : A ⥤δ B} {X n} (e : effacement F X n) : short_exact_sequence A :=
{ fst := X,
  snd := e.I,
  trd := limits.cokernel e.ι,
  f := e.ι,
  g := limits.cokernel.π _,
  exact' := abelian.exact_cokernel e.ι }

/-- An auxiliary definition used to obtain the isomorphism below -/
def effacement.cokernel_comparison {F : A ⥤δ B} {X n} (e : effacement F X n) :
  limits.cokernel ((F n).map (limits.cokernel.π e.ι)) ⟶ (F (n+1)).obj X :=
limits.cokernel.desc _ ((F.δ n).app e.ses) (F.exact_δ n e.ses).w

open_locale zero_object
instance effacement.epi_cokernel_comparison {F : A ⥤δ B} {X n} (e : effacement F X n) :
  epi e.cokernel_comparison :=
begin
  dsimp [effacement.cokernel_comparison],
  let t := _, change epi t,
  suffices : epi (limits.cokernel.π _ ≫ t),
  { resetI,
    apply epi_of_epi (limits.cokernel.π _) t },
  simp only [limits.cokernel.π_desc],
  have : exact ((F.δ n).app e.ses) ((F (n+1)).map e.ι) :=
    F.δ_exact n e.ses,
  rw e.w at this,

  apply abelian.pseudoelement.epi_of_pseudo_surjective,
  intros q,
  exact (abelian.pseudoelement.pseudo_exact_of_exact this).2 q (by simp),
end

/- This is true with fewer assumptions... -/
instance effacement.mono_cokernel_comparison {F : A ⥤δ B} {X n} (e : effacement F X n) :
  category_theory.mono e.cokernel_comparison :=
begin
  dsimp [effacement.cokernel_comparison],
  let t := _, change category_theory.mono t,
  suffices : exact ((F n).map (limits.cokernel.π e.ι)) ((F.δ n).app e.ses),
  exact abelian.category_theory.limits.cokernel.desc.category_theory.mono
    ((F n).map (limits.cokernel.π e.ι))
    ((F.δ n).app (effacement.ses e)) this,
  exact F.exact_δ n e.ses,
end

instance effacement.is_iso_cokernel_comparison {F : A ⥤δ B} {X n} (e : effacement F X n) :
  is_iso e.cokernel_comparison :=
is_iso_of_mono_of_epi _

/-- The cokernel isomorphism associated to an effacement. -/
def effacement.cokernel_iso {F : A ⥤δ B} {X n} (e : effacement F X n) :
  limits.cokernel ((F n).map (limits.cokernel.π e.ι)) ≅ (F (n+1)).obj X :=
as_iso e.cokernel_comparison

@[simp, reassoc]
lemma effacement.cokernel_iso_spec {F : A ⥤δ B} {X n} (e : effacement F X n) :
  limits.cokernel.π _ ≫ e.cokernel_iso.hom =
  (F.δ n).app e.ses :=
limits.cokernel.π_desc _ _ _

/-- An auxiliary definition used in `lift` below. -/
def effacement.lift_app_aux {F G : A ⥤δ B} {X n}
  (η : F n ⟶ G n) (e : effacement F X n) :
  (F (n+1)).obj X ⟶ (G (n+1)).obj X :=
e.cokernel_iso.inv ≫
limits.cokernel.desc _
(η.app _ ≫ (G.δ n).app e.ses)
begin
  rw [← category.assoc, η.naturality, category.assoc],
  erw (G.exact_δ n e.ses).w,
  rw [limits.comp_zero]
end

/-- An auxiliary definition used in `lift` below. -/
def effacement.map_ses {F : A ⥤δ B} {X n}
  (e₁ e₂ : effacement F X n) (q : e₁ ⟶ e₂) :
  e₁.ses ⟶ e₂.ses :=
{ fst := 𝟙 _,
  snd := q.t,
  trd := begin
    refine limits.cokernel.desc _ _ _,
    refine _ ≫ limits.cokernel.π _,
    exact q.t,
    rw [← category.assoc, q.w, limits.cokernel.condition]
  end,
  sq1' := by { simp only [category.id_comp], exact q.w.symm },
  sq2' := begin
    erw limits.cokernel.π_desc,
    refl,
  end }


lemma effacement.lift_app_aux_eq_of_hom
  {F G : A ⥤δ B} {X n}
  (η : F n ⟶ G n) (e₁ e₂ : effacement F X n) (q : e₁ ⟶ e₂) :
  e₁.lift_app_aux η = e₂.lift_app_aux η :=
begin
  dsimp only [effacement.lift_app_aux],
  rw iso.inv_comp_eq,
  apply limits.coequalizer.hom_ext,
  simp only [limits.cokernel.π_desc, effacement.cokernel_iso_spec_assoc],
  rw ← category.assoc, let t := _, change _ = t ≫ _,
  have ht : t = (F n).map (e₁.map_ses e₂ q).trd ≫ limits.cokernel.π _,
  { dsimp [t], rw iso.comp_inv_eq,
    simp only [category.assoc, effacement.cokernel_iso_spec],
    erw (F.δ n).naturality (e₁.map_ses e₂ q),
    dsimp [effacement.map_ses],
    simp },
  rw ht, clear ht t,
  simp only [category.assoc, limits.cokernel.π_desc],
  erw [nat_trans.naturality_assoc],
  congr' 1,
  erw (G.δ n).naturality (e₁.map_ses e₂ q),
  symmetry,
  convert category.comp_id _,
  exact functor.map_id _ _,
end

lemma effacement.lift_app_aux_well_defined
  {F G : A ⥤δ B} {X n}
  (η : F n ⟶ G n) (e₁ e₂ : effacement F X n) :
  e₁.lift_app_aux η = e₂.lift_app_aux η :=
begin
  let II := limits.biprod e₁.I e₂.I,
  let ι : X ⟶ II := limits.biprod.lift e₁.ι e₂.ι,
  let e : effacement F X n := ⟨II, ι, _⟩, -- use additivity of `F n`.
  swap,
  { haveI : limits.preserves_binary_biproducts (F (n+1)) :=
      limits.preserves_binary_biproducts_of_preserves_biproducts (F (n + 1)),
    let E : (F (n + 1)).obj (e₁.I ⊞ e₂.I) ≅ (F (n + 1)).obj (e₁.I) ⊞ (F (n+1)).obj (e₂.I) :=
      functor.map_biprod (F (n+1)) _ _,
    rw [← cancel_mono E.hom, limits.zero_comp],
    rw functor.map_biprod_hom,
    apply limits.biprod.hom_ext,
    { simp only [category.assoc, limits.biprod.lift_fst, limits.zero_comp],
      simp only [← functor.map_comp, limits.biprod.lift_fst, e₁.w] },
    { simp only [category.assoc, limits.biprod.lift_snd, limits.zero_comp],
      simp only [← functor.map_comp, limits.biprod.lift_snd, e₂.w] } },
  let π₁ : e ⟶ e₁ := ⟨limits.biprod.fst, _⟩,
  swap, { dsimp [e], simp, },
  let π₂ : e ⟶ e₂ := ⟨limits.biprod.snd, _⟩,
  swap, { dsimp [e], simp, },
  rw ← effacement.lift_app_aux_eq_of_hom η _ _ π₁,
  rw ← effacement.lift_app_aux_eq_of_hom η _ _ π₂,
end

lemma effacement.lift_naturality
  {F G : A ⥤δ B} {X Y n}
  (η : F n ⟶ G n) (e₁ : effacement F X n) (e₂ : effacement F Y n) (f : X ⟶ Y) :
  e₁.lift_app_aux η ≫ (G (n+1)).map f =
  (F (n+1)).map f ≫ e₂.lift_app_aux η :=
begin
  let e₁' : effacement F X n :=
    ⟨limits.biprod e₁.I e₂.I, limits.biprod.lift e₁.ι (f ≫ e₂.ι), _⟩, -- again, additivity
  swap,
  { haveI : limits.preserves_binary_biproducts (F (n+1)) :=
      limits.preserves_binary_biproducts_of_preserves_biproducts (F (n + 1)),
    let E : (F (n + 1)).obj (e₁.I ⊞ e₂.I) ≅ (F (n + 1)).obj (e₁.I) ⊞ (F (n+1)).obj (e₂.I) :=
      functor.map_biprod (F (n+1)) _ _,
    rw [← cancel_mono E.hom, limits.zero_comp],
    rw functor.map_biprod_hom,
    apply limits.biprod.hom_ext,
    simp only [category.assoc, limits.biprod.lift_fst, limits.zero_comp],
    simp only [← functor.map_comp, limits.biprod.lift_fst],
    exact e₁.w,
    simp only [category.assoc, limits.biprod.lift_snd, limits.zero_comp],
    simp only [← functor.map_comp, limits.biprod.lift_snd],
    simp only [functor.map_comp, e₂.w, limits.comp_zero] },
  rw e₁.lift_app_aux_well_defined η e₁',
  dsimp [effacement.lift_app_aux],
  simp only [category.assoc, iso.inv_comp_eq],
  apply limits.coequalizer.hom_ext,
  simp only [limits.coequalizer_as_cokernel, limits.cokernel.π_desc_assoc, category.assoc],
  erw limits.cokernel.π_desc_assoc,
  let q : e₁'.ses ⟶ e₂.ses := ⟨f, limits.biprod.snd,
    limits.cokernel.desc _ (limits.biprod.snd ≫ limits.cokernel.π _) _, _, _⟩,
  erw ← (F.δ n).naturality_assoc q,
  erw ← (G.δ n).naturality q,
  dsimp,
  have : (F.δ n).app e₂.ses ≫ e₂.cokernel_iso.inv = limits.cokernel.π _,
  { rw iso.comp_inv_eq, simp, },
  rw reassoc_of this, clear this,
  simp only [category.assoc, limits.cokernel.π_desc],
  erw ← nat_trans.naturality_assoc,
  refl,
  { dsimp [e₁'],
    simp },
  { dsimp [e₁', effacement.ses],
    simp },
  { dsimp [e₁', effacement.ses], simp, },
end

lemma effacement.lift_δ_naturality
  {F G : A ⥤δ B} {n}
  (η : F n ⟶ G n) (S : short_exact_sequence A)
  (e₁ : effacement F S.fst n) (e₂ : effacement F S.snd n) :
  (F.δ n).app S ≫ e₁.lift_app_aux η =
  η.app _ ≫ (G.δ _).app S :=
begin
  let e₁' : effacement F S.fst n :=
  ⟨e₂.I, S.f ≫ e₂.ι, by simp [e₂.w]⟩,
  rw e₁.lift_app_aux_well_defined η e₁',
  let q : S ⟶ e₁'.ses :=
    ⟨𝟙 _, e₂.ι, S.exact'.epi_desc (e₂.ι ≫ limits.cokernel.π _) _, _, _⟩,
  dsimp only [effacement.lift_app_aux],
  have : (F.δ n).app S ≫ e₁'.cokernel_iso.inv = (F n).map q.trd ≫
    limits.cokernel.π _,
  { rw iso.comp_inv_eq,
    simp,
    erw (F.δ n).naturality q,
    dsimp,
    simp only [functor.map_id, category.comp_id] },
  slice_lhs 1 2
  { erw this },
  simp only [category.assoc, limits.cokernel.π_desc],
  erw η.naturality_assoc,
  congr' 1,
  erw (G.δ n).naturality q, convert category.comp_id _,
  { dsimp, simpa only [functor.map_id], },
  rw ← category.assoc, exact limits.cokernel.condition _,
  { dsimp, simpa },
  { dsimp, simpa only [exact.comp_epi_desc] }
end

/-- An auxiliary definition used in `lift` below. -/
def effacable.lift_component (F G : A ⥤δ B) [effacable F] (n) (η : F n ⟶ G n) :
  F (n+1) ⟶ G (n+1) :=
{ app := λ X, (choose_effacement F X n).lift_app_aux η,
  naturality' := begin
    intros X Y f,
    symmetry,
    apply effacement.lift_naturality,
  end }

/-- The lift of η0. -/
noncomputable
def effacable.lift (F G : A ⥤δ B) [effacable F] (η0 : F 0 ⟶ G 0) : Π n, F n ⟶ G n
| 0 := η0
| (n+1) := effacable.lift_component _ _ _ (effacable.lift n)

/-- The lift of η0, as an actual delta functor. -/
def effacable.lift_with_δ (F G : A ⥤δ B) [effacable F] (η0 : F 0 ⟶ G 0) :
  F ⟶ G :=
{ η := effacable.lift _ _ η0,
  comm' := begin
    intros n, ext S : 2,
    dsimp,
    rcases n with (_|n),
    { dsimp [effacable.lift],
      apply effacement.lift_δ_naturality,
      apply choose_effacement },
    { dsimp [effacable.lift],
      apply effacement.lift_δ_naturality,
      apply choose_effacement },
  end }

lemma effacable.lift_with_δ_unique (F G : A ⥤δ B) [effacable F] (η0 : F 0 ⟶ G 0)
  (η : F ⟶ G) (hη : η 0 = η0) : η = effacable.lift_with_δ F G η0 :=
begin
  ext1 n, induction n with n hn,
  { rw hη, refl },
  { ext T, dsimp [effacable.lift_with_δ] at ⊢ hn,
    change _ = ((effacable.lift F G η0) _).app _,
    dsimp [effacable.lift],
    change _ = effacable.lift F G η0 n at hn,
    erw ← hn,
    dsimp [effacable.lift_component],
    dsimp [effacement.lift_app_aux],
    rw iso.eq_inv_comp,
    apply limits.coequalizer.hom_ext,
    dsimp,
    simp only [effacement.cokernel_iso_spec_assoc, limits.cokernel.π_desc],
    have := effacement.lift_δ_naturality (η n) ((choose_effacement F T n).ses)
      (choose_effacement _ _ _) (choose_effacement _ _ _),
    erw ← this, congr' 1,
    dsimp only [effacement.lift_app_aux],
    rw iso.eq_inv_comp,

    apply limits.coequalizer.hom_ext,
    simp only [effacement.cokernel_iso_spec_assoc, limits.cokernel.π_desc],
    clear this,
    have := η.comm' n,
    apply_fun (λ e, e.app ((choose_effacement F (choose_effacement F T n).ses.fst n).ses)) at this,
    exact this },
end

end tohoku
open tohoku

theorem universal_of_effacable (F : A ⥤δ B) [effacable F] : universal F :=
begin
  constructor, intros G η0,
  use effacable.lift_with_δ F G η0,
  split,
  { ext, refl, },
  { intros η hη, apply effacable.lift_with_δ_unique, exact hη, }
end

-- Sketch:
-- TODO: Prove stacks tag 010T. -- DONE!
-- TODO: Construct `Ext^*(-,X)` a delta functor (on objects!).
-- These should be functors `Aᵒᵖ ⥤ Ab` (assuming `A` has enough projectives).
-- Use `010T` to see that `Ext^*(-,X)` is universal.

end delta_functor

end category_theory
