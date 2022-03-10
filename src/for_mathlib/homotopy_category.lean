import algebra.homology.homotopy_category
import for_mathlib.homological_complex_shift

universes v u

open_locale classical
noncomputable theory

open category_theory category_theory.limits homological_complex

variables {ι : Type*}
variables {V : Type u} [category.{v} V] [preadditive V]
variables {c : complex_shape ι}

namespace category_theory

namespace quotient

variables {𝒞 : Type*} [category 𝒞] {r : hom_rel 𝒞} [congruence r]
variables {X Y : 𝒞} {f g : X ⟶ Y}

lemma comp_closure.rel (h : comp_closure r f g) : r f g :=
by { cases h, apply congruence.comp_left, apply congruence.comp_right, assumption }

end quotient

end category_theory

namespace homotopy

variables {C D : homological_complex V c} {f f₁ f₂ g g₁ g₂ : C ⟶ D}

@[simps {fully_applied := ff}]
protected def neg (h : homotopy f g) : homotopy (-f) (-g) :=
{ hom := -h.hom,
  zero' := λ i j H, by { dsimp, rw [h.zero i j H, neg_zero] },
  comm := λ i, by simp only [neg_f_apply, add_monoid_hom.map_neg, h.comm, neg_add] }

@[simps {fully_applied := ff}]
def add_left (f : C ⟶ D) (h : homotopy g₁ g₂) : homotopy (f + g₁) (f + g₂) :=
{ comm := λ i, by { simp only [add_f_apply, h.comm], rw [add_comm, add_comm (f.f i), ← add_assoc] },
  .. h }

@[simps {fully_applied := ff}]
def add_right (h : homotopy f₁ f₂) (g : C ⟶ D) : homotopy (f₁ + g) (f₂ + g) :=
{ comm := λ i, by simp only [add_f_apply, h.comm, add_assoc],
  .. h }

@[simps {fully_applied := ff}]
def sub_left (f : C ⟶ D) (h : homotopy g₁ g₂) : homotopy (f - g₁) (f - g₂) :=
{ comm := λ i, by simp only [h.comm, add_f_apply, neg_f_apply, neg_hom, sub_eq_add_neg,
    add_monoid_hom.map_neg, add_comm _ (f.f i), ← add_assoc, neg_add],
  .. h.neg }

@[simps {fully_applied := ff}]
def sub_right (h : homotopy f₁ f₂) (g : C ⟶ D) : homotopy (f₁ - g) (f₂ - g) :=
{ comm := λ i, by simp only [sub_f_apply, h.comm, add_sub],
  .. h }

end homotopy

namespace homotopy_category
/-
Generalize this stuff to suitable quotient categories?
-/

variables (A B : homotopy_category V c)

@[simp] lemma quot_mk {A B : homological_complex V c} (f : A ⟶ B) :
  quot.mk _ f = (quotient V c).map f := rfl

instance : has_zero (A ⟶ B) :=
⟨(quotient V c).map 0⟩

instance : has_neg (A ⟶ B) :=
⟨quot.lift (λ f, (quotient V c).map (-f))
  (λ (f g : A.as ⟶ B.as) (h : quotient.comp_closure (homotopic V c) f g),
    eq_of_homotopy _ _ h.rel.some.neg)⟩

instance : has_add (A ⟶ B) :=
⟨quot.lift₂ (λ f g, (quotient V c).map (f + g))
  (λ (f g₁ g₂ : A.as ⟶ B.as) (h : quotient.comp_closure (homotopic V c) g₁ g₂),
    eq_of_homotopy _ _ (h.rel.some.add_left _))
  (λ (f₁ f₂ g : A.as ⟶ B.as) (h : quotient.comp_closure (homotopic V c) f₁ f₂),
    eq_of_homotopy _ _ (h.rel.some.add_right g))⟩

instance : has_sub (A ⟶ B) :=
⟨quot.lift₂ (λ f g, (quotient V c).map (f - g))
  (λ (f g₁ g₂ : A.as ⟶ B.as) (h : quotient.comp_closure (homotopic V c) g₁ g₂),
    eq_of_homotopy _ _ (h.rel.some.sub_left _))
  (λ (f₁ f₂ g : A.as ⟶ B.as) (h : quotient.comp_closure (homotopic V c) f₁ f₂),
    eq_of_homotopy _ _ (h.rel.some.sub_right g))⟩

instance has_nsmul : has_scalar ℕ (A ⟶ B) := ⟨λ n, nsmul_rec n⟩

instance has_zsmul : has_scalar ℤ (A ⟶ B) := ⟨λ n, zsmul_rec n⟩

lemma quotient_map_neg {A B : homological_complex V c} (f : A ⟶ B) :
(quotient V c).map (-f) = -(quotient V c).map f := rfl

lemma quotient_map_add {A B : homological_complex V c} (f g : A ⟶ B) :
  (quotient V c).map (f + g) = (quotient V c).map f + (quotient V c).map g := rfl

lemma quotient_map_sub {A B : homological_complex V c} (f g : A ⟶ B) :
  (quotient V c).map (f - g) = (quotient V c).map f - (quotient V c).map g := rfl

lemma quotient_map_nsmul {A B : homological_complex V c} (n : ℕ) (f : A ⟶ B) :
(quotient V c).map (n • f) = n • (quotient V c).map f :=
begin
  induction n with n ih,
  { rw zero_smul, refl },
  { rw [succ_nsmul, quotient_map_add, ih], refl, }
end

lemma quotient_map_zsmul {A B : homological_complex V c} (n : ℤ) (f : A ⟶ B) :
(quotient V c).map (n • f) = n • (quotient V c).map f :=
begin
  cases n,
  { rw [of_nat_zsmul, quotient_map_nsmul], refl },
  { rw [zsmul_neg_succ_of_nat, quotient_map_neg, quotient_map_nsmul], refl, }
end

instance : add_comm_group (A ⟶ B) :=
function.surjective.add_comm_group (λ f, (quotient V c).map f) (surjective_quot_mk _)
  rfl (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl)
  (λ f n, quotient_map_nsmul n f) (λ f n, quotient_map_zsmul n f)

instance : preadditive (homotopy_category V c) :=
{ add_comp' := λ X Y Z f₁ f₂ g,
  begin
    apply quot.induction_on₃ f₁ f₂ g, clear f₁ f₂ g,
    intros f₁ f₂ g,
    repeat { erw quot_mk },
    rw [← quotient_map_add],
    calc (quotient V c).map (f₁ + f₂) ≫ (quotient V c).map g
        = (quotient V c).map ((f₁ + f₂) ≫ g) : by rw (quotient V c).map_comp
    ... = (quotient V c).map (f₁ ≫ g + f₂ ≫ g) : by rw preadditive.add_comp
    ... = (quotient V c).map (f₁ ≫ g) + (quotient V c).map (f₂ ≫ g) :
      by rw quotient_map_add,
  end,
  comp_add' := λ X Y Z f g₁ g₂,
  begin
    apply quot.induction_on₃ f g₁ g₂, clear f g₁ g₂,
    intros f g₁ g₂,
    repeat { erw quot_mk },
    rw [← quotient_map_add],
    calc (quotient V c).map f ≫ (quotient V c).map (g₁ + g₂)
        = (quotient V c).map (f ≫ (g₁ + g₂)) : by rw (quotient V c).map_comp
    ... = (quotient V c).map (f ≫ g₁ + f ≫ g₂) : by rw preadditive.comp_add
    ... = (quotient V c).map (f ≫ g₁) + (quotient V c).map (f ≫ g₂) :
      by rw quotient_map_add,
  end }

instance quotient.additive : (quotient V c).additive := {}

attribute[derive [full]] quotient

open_locale zero_object

instance [has_zero_object V] : has_zero_object (homotopy_category V c) :=
{ zero := ⟨0⟩,
  unique_to := λ X, ⟨⟨0⟩, λ f, by { induction f using quot.induction_on, dsimp, erw quot_mk,
    rw [← (quotient V c).map_zero], congr, ext }⟩,
  unique_from := λ X, ⟨⟨0⟩, λ f, by { induction f using quot.induction_on, dsimp, erw quot_mk,
    rw [← (quotient V c).map_zero], congr, ext }⟩ }

instance shift_functor_additive (n : ℤ) :
  (category_theory.shift_functor (homotopy_category V (complex_shape.up ℤ)) n).additive :=
{}


end homotopy_category
