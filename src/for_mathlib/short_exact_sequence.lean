import category_theory.preadditive
import category_theory.abelian.projective

import data.matrix.notation

import for_mathlib.abelian_category
import for_mathlib.fin_functor

noncomputable theory

open category_theory
open category_theory.limits

universes v u

namespace category_theory
variables (𝒞 : Type u) [category.{v} 𝒞]

@[ext]
structure short_exact_sequence [has_images 𝒞] [has_zero_morphisms 𝒞] [has_kernels 𝒞] :=
(fst snd trd : 𝒞)
(f : fst ⟶ snd)
(g : snd ⟶ trd)
(mono : mono f)
(epi : epi g)
(exact : exact f g)

namespace short_exact_sequence

variables {𝒞} [has_images 𝒞] [has_zero_morphisms 𝒞] [has_kernels 𝒞]

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

@[simps] def f_nat : Fst 𝒞 ⟶ Snd 𝒞 :=
{ app := λ A, A.f,
  naturality' := λ A B f, f.sq1 }

@[simps] def g_nat : Snd 𝒞 ⟶ Trd 𝒞 :=
{ app := λ A, A.g,
  naturality' := λ A B f, f.sq2 }

instance : has_zero_morphisms (short_exact_sequence 𝒞) :=
{ has_zero := λ A B, ⟨{ fst := 0, snd := 0, trd := 0 }⟩,
  comp_zero' := by { intros, ext; apply comp_zero },
  zero_comp' := by { intros, ext; apply zero_comp }, }
.

variables {𝒞}

protected def functor (A : short_exact_sequence 𝒞) : fin 3 ⥤ 𝒞 :=
fin3_functor_mk ![A.1, A.2, A.3] A.f A.g

def functor_map {A B : short_exact_sequence 𝒞} (f : A ⟶ B) :
  Π i, A.functor.obj i ⟶ B.functor.obj i
| ⟨0,h⟩ := f.1
| ⟨1,h⟩ := f.2
| ⟨2,h⟩ := f.3
| ⟨i+3,hi⟩ := by { exfalso, revert hi, dec_trivial }

meta def aux_tac : tactic unit :=
`[simp only [hom_of_le_refl, functor.map_id, category.id_comp, category.comp_id]]

lemma functor_map_naturality {A B : short_exact_sequence 𝒞} (f : A ⟶ B) :
  ∀ (i j : fin 3) (hij : i ≤ j),
    functor_map f i ≫ B.functor.map hij.hom = A.functor.map hij.hom ≫ functor_map f j
| ⟨0,hi⟩ ⟨0,hj⟩ hij := by aux_tac
| ⟨1,hi⟩ ⟨1,hj⟩ hij := by aux_tac
| ⟨2,hi⟩ ⟨2,hj⟩ hij := by aux_tac
| ⟨0,hi⟩ ⟨1,hj⟩ hij := f.sq1
| ⟨1,hi⟩ ⟨2,hj⟩ hij := f.sq2
| ⟨i+3,hi⟩ _ _ := by { exfalso, revert hi, dec_trivial }
| _ ⟨j+3,hj⟩ _ := by { exfalso, revert hj, dec_trivial }
| ⟨i+1,hi⟩ ⟨0,hj⟩ H := by { exfalso, revert H, dec_trivial }
| ⟨i+2,hi⟩ ⟨1,hj⟩ H := by { exfalso, revert H, dec_trivial }
| ⟨0,hi⟩ ⟨2,hj⟩ hij :=
begin
  have h01 : (0 : fin 3) ⟶ 1 := hom_of_le dec_trivial,
  have h12 : (1 : fin 3) ⟶ 2 := hom_of_le dec_trivial,
  calc functor_map f ⟨0, hi⟩ ≫ B.functor.map hij.hom
      = functor_map f ⟨0, hi⟩ ≫ B.functor.map h01 ≫ B.functor.map h12 : _
  ... = (functor_map f ⟨0, hi⟩ ≫ B.functor.map h01) ≫ B.functor.map h12 : by rw category.assoc
  ... = (A.functor.map h01 ≫ functor_map f _) ≫ B.functor.map h12 : _
  ... = A.functor.map h01 ≫ functor_map f _ ≫ B.functor.map h12 : category.assoc _ _ _
  ... = A.functor.map h01 ≫ A.functor.map h12 ≫ functor_map f _ : _
  ... = A.functor.map hij.hom ≫ functor_map f ⟨2, hj⟩ : _,
  { rw [← functor.map_comp], congr, },
  { congr' 1, exact f.sq1 },
  { congr' 1, exact f.sq2 },
  { rw [← functor.map_comp_assoc], congr, },
end

def Functor : short_exact_sequence 𝒞 ⥤ fin 3 ⥤ 𝒞 :=
{ obj := short_exact_sequence.functor,
  map := λ A B f,
  { app := functor_map f,
    naturality' := λ i j hij, (functor_map_naturality f i j hij.le).symm },
  map_id' := λ A, by { ext i, fin_cases i; refl },
  map_comp' := λ A B C f g, by { ext i, fin_cases i; refl } }

end short_exact_sequence

namespace short_exact_sequence

open category_theory.preadditive

variables {𝒞} [preadditive 𝒞] [has_images 𝒞] [has_kernels 𝒞]
variables (A B : short_exact_sequence 𝒞)

local notation `π₁` := congr_arg _root_.prod.fst
local notation `π₂` := congr_arg _root_.prod.snd

protected def hom_inj (f : A ⟶ B) : (A.1 ⟶ B.1) × (A.2 ⟶ B.2) × (A.3 ⟶ B.3) := ⟨f.1, f.2, f.3⟩

protected lemma hom_inj_injective : function.injective (short_exact_sequence.hom_inj A B) :=
λ f g h, let aux := π₂ h in
by { ext; [have := π₁ h, have := π₁ aux, have := π₂ aux]; exact this, }

instance : has_add (A ⟶ B) :=
{ add := λ f g,
  { fst := f.1 + g.1,
    snd := f.2 + g.2,
    trd := f.3 + g.3,
    sq1' := by { rw [add_comp, comp_add, f.sq1, g.sq1], },
    sq2' := by { rw [add_comp, comp_add, f.sq2, g.sq2], } } }

instance : has_neg (A ⟶ B) :=
{ neg := λ f,
  { fst := -f.1,
    snd := -f.2,
    trd := -f.3,
    sq1' := by { rw [neg_comp, comp_neg, f.sq1], },
    sq2' := by { rw [neg_comp, comp_neg, f.sq2], } } }

instance : has_sub (A ⟶ B) :=
{ sub := λ f g,
  { fst := f.1 - g.1,
    snd := f.2 - g.2,
    trd := f.3 - g.3,
    sq1' := by { rw [sub_comp, comp_sub, f.sq1, g.sq1], },
    sq2' := by { rw [sub_comp, comp_sub, f.sq2, g.sq2], } } }

variables (𝒞)

instance : preadditive (short_exact_sequence 𝒞) :=
{ hom_group := λ A B, (short_exact_sequence.hom_inj_injective A B).add_comm_group _
  rfl (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl),
  add_comp' := by { intros, ext; apply add_comp },
  comp_add' := by { intros, ext; apply comp_add }, }
.

instance Fst_additive : (Fst 𝒞).additive := {}
instance Snd_additive : (Snd 𝒞).additive := {}
instance Trd_additive : (Trd 𝒞).additive := {}

end short_exact_sequence
