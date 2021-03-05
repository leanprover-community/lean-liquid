import system_of_complexes.basic
import for_mathlib.normed_group_quotient

/-!
# Soft truncation

In this file we define soft truncation functors
for (systems of) complexes of normed groups.

We call these `soft_truncation'` to distinguish them from the usual soft truncation functors.
The difference is solely in the definition of the object in degree `0`.
Usually this object is defined as `C 0` modulo the kernel of `d : C 0 ⟶ C 1`.
Instead, we define it as `C 0` modulo the image of `d : C (-1) ⟶ C 0`.
Hence the two definitions agree iff `C` is exact in degree `0`.

-/

noncomputable theory
open_locale nnreal

open category_theory category_theory.limits

section has_succ

class has_succ (α : Type*) := (succ : α → α)

-- I can't find that Turkish(?) symbol on my keyboard :-(
notation `Sc` := has_succ.succ

def int.has_succ : has_succ ℤ := ⟨λ z, z + 1⟩

local attribute [instance] int.has_succ

def dsource (n : ℤ) : Sc n = n + 1 := rfl
def dtarget (n : ℤ) : Sc (n - 1) = n := sub_add_cancel n 1

end has_succ

section cochain_complex'

universes v u

structure cochain_complex' (𝒞 : Type u) [category.{v} 𝒞] [has_zero_morphisms 𝒞]
  (α : Type*) [has_succ α] :=
(X : α → 𝒞)
(d {i j : α} (h : Sc i = j) : X i ⟶ X j)
(d_squared' {i j k : α} (hij : Sc i = j) (hjk : Sc j = k) : (d hij) ≫ (d hjk) = 0)

variables {𝒞 : Type u} [category.{v} 𝒞] [has_zero_morphisms 𝒞]
  {α : Type*} [has_succ α]

structure hom (X Y : cochain_complex' 𝒞 α) :=
(f : ∀ (i : α), X.X i ⟶ Y.X i)
(comm' : ∀ {i j : α} (hij : Sc i = j), (X.d hij ≫ f j = f i ≫ Y.d hij))

@[ext] lemma hom.ext {X Y : cochain_complex' 𝒞 α} (f g : hom X Y) : f.f = g.f → f = g :=
begin
  cases f, cases g,
  simp,
end

instance : category (cochain_complex' 𝒞 α) :=
{ hom := hom,
  id := λ _, { f := λ _, 𝟙 _, comm' := λ _ _ _, by rw [category.id_comp, category.comp_id] },
  comp := λ X Y Z fXY fYZ, { f := λ i, fXY.f i ≫ fYZ.f i, comm' := λ i j hij, by
    rw [← category_theory.category.assoc, fXY.comm' hij, category_theory.category.assoc,
        fYZ.comm' hij, category_theory.category.assoc] },
  id_comp' := λ X Y f, begin
    simp,
    ext,
    refl,
  end,
  comp_id' := λ X Y f, begin
    simp,
    ext,
    refl,
  end,
  assoc' := λ W X Y Z f g h, by simp only [category.assoc] }

local attribute [instance] int.has_succ

variable  (C : cochain_complex' 𝒞 ℤ)

lemma d_squared_left (n : ℤ) : C.d (dsource n) ≫ C.d (dsource (n + 1)) = 0 :=
C.d_squared' (dsource n) (dsource (n + 1))

lemma d_squared_middle (n : ℤ) : C.d (dtarget n) ≫ C.d (dsource n) = 0 :=
C.d_squared' (dtarget n) (dsource n)

lemma d_squared_right (n : ℤ) : C.d (dtarget (n - 1)) ≫ C.d (dtarget n) = 0 :=
C.d_squared' (dtarget (n - 1)) (dtarget n)

end cochain_complex'

namespace NormedGroup
open quotient_add_group

namespace soft_truncation'

local attribute [instance] int.has_succ

def X (C : cochain_complex' NormedGroup ℤ) : ℤ → NormedGroup
| -[1+n]  := 0
| 0       := coker (C.d (dtarget 0))
| (n+1:ℕ) := C.X (n+1)

def d (C : cochain_complex' NormedGroup ℤ) : ∀ {i j : ℤ} (h : Sc i = j), X C i ⟶ X C j
| -[1+n] _ _ := 0
| 0 1 rfl := coker.lift (d_squared_right C 1)
| (n+1 : ℕ) (m+1 : ℕ) h := C.d h

lemma d_squared' (C : cochain_complex' NormedGroup ℤ) :
  ∀ {i j k:ℤ} (hij : Sc i = j) (hjk : Sc j = k), d C hij ≫ d C hjk = 0
| -[1+n] _ _ _ _ := show 0 ≫ _ = 0, by rw zero_comp
| 0 1 2 rfl rfl := show coker.lift (d_squared_right C 1) ≫ C.d (dsource 1) = 0,
begin
  rw coker.lift_comp_eq_lift,
  convert coker.lift_zero,
  exact d_squared_middle C 1,
end
| (n+1:ℕ) (p+1:ℕ) (q+1:ℕ) rfl rfl := C.d_squared' rfl rfl

@[simps]
def obj (C : cochain_complex' NormedGroup ℤ) :
  cochain_complex' NormedGroup ℤ :=
{ X := X C,
  d := λ _ _, d C,
  d_squared' := λ _ _ _, d_squared' C }

def map_f {C₁ C₂ : cochain_complex' NormedGroup ℤ} (f : C₁ ⟶ C₂) :
  Π i:ℤ, X C₁ i ⟶ X C₂ i
| -[1+n]  := 0
| 0       := coker.map (f.comm' (dtarget 0))
| (n+1:ℕ) := f.f (n+1)

lemma map_comm {C₁ C₂ : cochain_complex' NormedGroup ℤ} (f : C₁ ⟶ C₂) :
  Π {i j:ℤ} (hij : Sc i = j), d C₁ hij ≫ map_f f j = map_f f i ≫ d C₂ hij
|  -[1+n]       _   _ := show 0 ≫ _ = _ ≫ 0, by rw [zero_comp, comp_zero]
|       0       1   h := coker.map_lift_comm (f.comm' (dtarget 1)) -- some quotient.lift or quotient.map ??
| (n+1:ℕ) (m+1:ℕ) rfl := f.comm' rfl

def map {C₁ C₂ : cochain_complex' NormedGroup ℤ} (f : C₁ ⟶ C₂) :
  obj C₁ ⟶ obj C₂ :=
{ f := map_f f,
  comm' := λ _ _, map_comm f}

end soft_truncation'

local attribute [instance] int.has_succ

@[simps]
def soft_truncation' : cochain_complex' NormedGroup ℤ ⥤ cochain_complex' NormedGroup ℤ :=
{ obj := λ C, soft_truncation'.obj C,
  map := λ C₁ C₂ f, soft_truncation'.map f,
  map_id' := λ X, by sorry,
  map_comp' := sorry }

end NormedGroup

namespace system_of_complexes

variables (C : system_of_complexes)

@[simps]
def soft_truncation' : system_of_complexes ⥤ system_of_complexes :=
(whiskering_right _ _ _).obj $ NormedGroup.soft_truncation'

lemma soft_truncation'_d_neg (c : ℝ≥0) (i : ℤ) (hi : i < 0) :
  (d : (soft_truncation'.obj C) c i ⟶ _) = 0 := sorry

variables (k K : ℝ≥0) (m : ℤ) [hk : fact (1 ≤ k)] (c₀ : ℝ≥0)
include hk

lemma soft_truncation'_is_bounded_exact_iff
  (hC : ∀ c, (d : (soft_truncation'.obj C) c (-2) ⟶ _) = 0) :
  (soft_truncation'.obj C).is_bounded_exact k K m c₀ ↔ C.is_bounded_exact k K m c₀ :=
sorry

lemma soft_truncation'_is_weak_bounded_exact_iff
  (hC : ∀ c, (d : (soft_truncation'.obj C) c (-2) ⟶ _) = 0) :
  (soft_truncation'.obj C).is_weak_bounded_exact k K m c₀ ↔ C.is_weak_bounded_exact k K m c₀ :=
sorry


/-
TODO

* lemmas for how `has_shift` interacts with bounded exactness
-/

end system_of_complexes
