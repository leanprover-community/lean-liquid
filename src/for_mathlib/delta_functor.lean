import category_theory.preadditive
import category_theory.abelian.projective

import for_mathlib.abelian_category

noncomputable theory

open category_theory
open category_theory.limits

universes v u

namespace category_theory
variables (𝒞 : Type u) [category.{v} 𝒞] [has_images 𝒞] [has_zero_morphisms 𝒞] [has_kernels 𝒞]

@[ext]
structure short_exact_sequence :=
(fst snd trd : 𝒞)
(f : fst ⟶ snd)
(g : snd ⟶ trd)
(mono : mono f)
(epi : epi g)
(exact : exact f g)

variables {𝒞}

namespace short_exact_sequence

@[ext]
structure hom (A B : short_exact_sequence 𝒞) :=
(fst : A.1 ⟶ B.1)
(snd : A.2 ⟶ B.2)
(trd : A.3 ⟶ B.3)
(sq1' : fst ≫ B.f = A.f ≫ snd . obviously)
(sq2' : snd ≫ B.g = A.g ≫ trd . obviously)

namespace hom

restate_axiom sq1' sq1
restate_axiom sq2' sq2

attribute [reassoc] sq1 sq2

end hom

instance : quiver (short_exact_sequence 𝒞) := ⟨hom⟩

@[simps]
def id (A : short_exact_sequence 𝒞) : A ⟶ A :=
{ fst := 𝟙 _,
  snd := 𝟙 _,
  trd := 𝟙 _,
  sq1' := by simp only [category.id_comp, category.comp_id],
  sq2' := by simp only [category.id_comp, category.comp_id], }

@[simps]
def comp {A B C : short_exact_sequence 𝒞} (f : A ⟶ B) (g : B ⟶ C) : A ⟶ C :=
{ fst := f.1 ≫ g.1,
  snd := f.2 ≫ g.2,
  trd := f.3 ≫ g.3,
  sq1' := by rw [category.assoc, hom.sq1, hom.sq1_assoc],
  sq2' := by rw [category.assoc, hom.sq2, hom.sq2_assoc], }

instance : category (short_exact_sequence 𝒞) :=
{ id := id,
  comp := λ A B C f g, comp f g,
  id_comp' := by { intros, ext; dsimp; simp only [category.id_comp], },
  comp_id' := by { intros, ext; dsimp; simp only [category.comp_id], },
  assoc' := by { intros, ext; dsimp; simp only [category.assoc], },
  .. (infer_instance : quiver (short_exact_sequence 𝒞)) }

variables (𝒞)

@[simps] def Fst : short_exact_sequence 𝒞 ⥤ 𝒞 :=
{ obj := fst, map := λ A B f, f.1 }

@[simps] def Snd : short_exact_sequence 𝒞 ⥤ 𝒞 :=
{ obj := snd, map := λ A B f, f.2 }

@[simps] def Trd : short_exact_sequence 𝒞 ⥤ 𝒞 :=
{ obj := trd, map := λ A B f, f.3 }

end short_exact_sequence

variables {C : Type u} [category.{v} C] {D : Type*} [category D]

variables [has_images C] [has_zero_morphisms C] [has_kernels C]
variables [has_images D] [has_zero_morphisms D] [has_kernels D]

/-- Cohomological covariant delta functor. -/
variables (C D)
structure delta_functor :=
(F : ℕ → C ⥤ D)
(δ' : Π (n : ℕ), short_exact_sequence.Trd C ⋙ (F n) ⟶ short_exact_sequence.Fst C ⋙ (F (n+1)))
(mono : ∀ (A : short_exact_sequence C), mono ((F 0).map A.f))
(exact' : ∀ (n : ℕ) (A : short_exact_sequence C), exact ((F n).map A.f) ((F n).map A.g))
(exact_δ' : ∀ (n : ℕ) (A : short_exact_sequence C), exact ((F n).map A.g) ((δ' n).app A))
(δ_exact' : ∀ (n : ℕ) (A : short_exact_sequence C), exact ((δ' n).app A) ((F (n+1)).map A.f))
variables {C D}

infixr ` ⥤δ  `:26 := delta_functor

namespace delta_functor

instance : has_coe_to_fun (C ⥤δ D) := ⟨_, λ F, F.F⟩

def δ (F : C ⥤δ D) (n : ℕ) : short_exact_sequence.Trd C ⋙ F n ⟶
  short_exact_sequence.Fst C ⋙ F (n+1) := F.δ' _

structure hom (F G : C ⥤δ D) :=
(η' : Π n : ℕ, F n ⟶ G n)
(w' : ∀ n, whisker_left _ (η' _) ≫ G.δ _ = F.δ n ≫ whisker_left _ (η' _) . obviously)

namespace hom

instance {F G : C ⥤δ D} : has_coe_to_fun (hom F G) := ⟨_,λ η, η.η'⟩

@[ext]
lemma ext {F G : C ⥤δ D} (f g : hom F G) : (∀ n, f n = g n) → f = g :=
by { intro h, cases f, cases g, congr' 1, ext1, apply h }

@[simp, reassoc]
lemma w {F G : C ⥤δ D} (e : hom F G) (n : ℕ) :
  whisker_left _ (e _) ≫ G.δ _ = F.δ n ≫ whisker_left _ (e _) := e.w' _

def id (F : C ⥤δ D) : hom F F := { η' := λ n, 𝟙 _ }

def comp {F G H : C ⥤δ D} (f : hom F G) (g : hom G H) : hom F H := { η' := λ n, f n ≫ g n }

@[simp]
lemma coe_id (F : C ⥤δ D) (n) : id F n = 𝟙 _ := rfl

@[simp]
lemma coe_comp {F G H : C ⥤δ D} (f : hom F G) (g : hom G H) (n) : f.comp g n = f n ≫ g n := rfl

end hom

instance : category (C ⥤δ D) :=
{ hom := λ F G, hom F G,
  id := hom.id,
  comp := λ F G H, hom.comp } .

class universal (F : C ⥤δ D) : Prop :=
(bij : ∀ G : C ⥤δ D, function.bijective (λ (e : hom F G), e 0))

variables (F : C ⥤δ D) [universal F]

def equiv {G : C ⥤δ D} : (F ⟶ G) ≃ (F 0 ⟶ G 0) :=
equiv.of_bijective _ $ universal.bij _

@[simp]
lemma equiv_coe {G : C ⥤δ D} (g : F ⟶ G) : F.equiv g = g 0 := rfl

def lift {G : C ⥤δ D} (η : F 0 ⟶ G 0) : F ⟶ G := F.equiv.symm η

@[simp]
lemma lift_spec {G : C ⥤δ D} (η : F 0 ⟶ G 0) : F.lift η 0 = η :=
by { change F.equiv (F.equiv.symm _) = _, simp only [equiv.apply_symm_apply] }

lemma lift_unique {G : C ⥤δ D} (h : F ⟶ G) (η : F 0 ⟶ G 0) :
  h 0 = η → h = F.lift η :=
begin
  intro hh,
  apply_fun F.equiv,
  convert hh using 1,
  simp,
end

@[ext]
lemma hom_ext {G : C ⥤δ D} (f g : F ⟶ G) : f 0 = g 0 → f = g :=
begin
  intro h,
  have : g = F.lift (g 0) := lift_unique _ _ _ rfl,
  rw this,
  apply lift_unique,
  exact h
end

@[simps hom inv]
def lift_iso {G : C ⥤δ D} [universal G] (η : F 0 ≅ G 0) : F ≅ G :=
{ hom := F.lift η.hom,
  inv := G.lift η.inv,
  hom_inv_id' := begin
    ext1,
    change F.lift η.hom 0 ≫ _ = _,
    simpa,
  end,
  inv_hom_id' := begin
    ext1,
    change G.lift η.inv 0 ≫ _ = _,
    simpa,
  end }

end delta_functor

end category_theory
