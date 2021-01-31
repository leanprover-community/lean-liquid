-- n©

import breen_deligne.basic

/-!

# Universality of universal maps

A `universal_map m n` in this repo is a formal `ℤ`-linear combination
of `m × n` matrices. In this file we show that to give a term of this
type is to give a collection of additive group homomorphisms `ℤ[A^m] → ℤ[A^n]`
for each abelian group `A`, functorial in `A`.


-/

noncomputable theory

@[simp, to_additive] lemma monoid_hom.inv_comp {M N A} {mM : monoid M} {gN : monoid N}
  {gG : comm_group A} (φ : N →* A) (ψ : M →* N) : φ⁻¹.comp ψ = (φ.comp ψ)⁻¹ :=
by { ext, simp only [function.comp_app, monoid_hom.inv_apply, monoid_hom.coe_comp]}

@[simp, to_additive] lemma monoid_hom.comp_inv {M A B} {mM : monoid M} {mA : comm_group A}
  {mB : comm_group B} (φ : A →* B) (ψ : M →* A) : φ.comp ψ⁻¹ = (φ.comp ψ)⁻¹ :=
by {ext, simp only [function.comp_app, monoid_hom.inv_apply, monoid_hom.map_inv, monoid_hom.coe_comp]}

-- @[simp, to_additive] lemma one_comp [monoid M] [monoid N] [monoid P] (f : M →* N) :
--   (1 : N →* P).comp f = 1 := rfl
-- @[simp, to_additive] lemma comp_one [monoid M] [monoid N] [monoid P] (f : N →* P) :
--   f.comp (1 : M →* N) = 1 :=
-- by { ext, simp only [map_one, coe_comp, function.comp_app, one_apply] }

-- @[to_additive] lemma mul_comp [monoid M] [comm_monoid N] [comm_monoid P]
--   (g₁ g₂ : N →* P) (f : M →* N) :
--   (g₁ * g₂).comp f = g₁.comp f * g₂.comp f := rfl
-- @[to_additive] lemma comp_mul [monoid M] [comm_monoid N] [comm_monoid P]
--   (g : N →* P) (f₁ f₂ : M →* N) :
--   g.comp (f₁ * f₂) = g.comp f₁ * g.comp f₂ :=
-- by { ext, simp only [mul_apply, function.comp_app, map_mul, coe_comp] }


-- get some notation working:
open_locale big_operators direct_sum

local attribute [instance] type_pow
local notation `ℤ[` A `]` := free_abelian_group A

universes u

def add_monoid_hom.pow {A : Type u} [add_comm_group A] {B : Type u} [add_comm_group B]
  (φ : A →+ B) (n : ℕ) : A^n →+ B^n :=
{ to_fun := (∘) φ,
  map_zero' := funext (λ _, φ.map_zero),
  map_add' := λ _ _, funext (λ _, φ.map_add _ _) }

lemma add_monoid_hom.pow_eval {A : Type u} [add_comm_group A] {B : Type u} [add_comm_group B]
  (φ : A →+ B) (n : ℕ) (as : A ^ n) (i : fin n) : φ.pow n as i = φ (as i) := rfl

namespace breen_deligne

section functorial_map_section

open free_abelian_group

@[ext] structure functorial_map (m n : ℕ) :=
(f (A : Type u) [add_comm_group A] : ℤ[A^m] →+ ℤ[A^n])
(functorial (A : Type u) [add_comm_group A] (B : Type u) [add_comm_group B] (φ : A →+ B) :
  (free_abelian_group.map (φ.pow n)).comp (f A) = (f B).comp (map (φ.pow m)))

variables {m n : ℕ}

namespace functorial_map

open add_monoid_hom

def add (F G : functorial_map m n) : functorial_map m n :=
{ f := λ A _, by exactI F.f A + G.f A,
  functorial := λ A _ B _ φ, by rw [comp_add, add_comp, F.functorial, G.functorial] }

instance : has_add (functorial_map m n) := ⟨add⟩

-- lemma add_assoc (F G H : functorial_map m n) : F + G + H = F + (G + H) :=
-- ext _ _ $ funext (λ A, funext (λ _, by exactI add_assoc _ _ _))

-- lemma add_comm (F G : functorial_map m n) : F + G = G + F :=
-- ext _ _ $ funext (λ A, funext (λ _, by exactI add_comm _ _))

def zero : functorial_map m n :=
{ f := λ A _, 0,
  functorial := by intros; simp }

instance : has_zero (functorial_map m n) := ⟨zero⟩

def neg (F : functorial_map m n) : functorial_map m n :=
{ f := λ A _, by exactI -F.f A,
  functorial := λ A _ B _ φ, by rw [comp_neg, neg_comp, F.functorial]}

instance : has_neg (functorial_map m n) := ⟨neg⟩

instance : add_comm_group (functorial_map m n) :=
{ add := (+),
  add_assoc := λ _ _ _, ext _ _ $ funext (λ A, funext (λ _, by exactI add_assoc _ _ _)),
  zero := 0,
  zero_add := λ _, ext _ _ $ funext (λ A, funext (λ _, by exactI zero_add _)),
  add_zero := λ _, ext _ _ $ funext (λ A, funext (λ _, by exactI add_zero _)),
  neg := has_neg.neg,
  add_left_neg := λ _, ext _ _ $ funext (λ A, funext (λ _, by exactI add_left_neg _)),
  add_comm := λ F G, ext _ _ $ funext (λ A, funext (λ _, by exactI add_comm _ _)) }

end functorial_map

end functorial_map_section

open universal_map
open add_monoid_hom

/-
simplify tactic failed to simplify
state:
m n : ℕ,
U : universal_map m n,
A : Type ?,
_x : add_comm_group A,
B : Type ?,
_x : add_comm_group B,
φ : A →+ B
⊢ (map ⇑(φ.pow n)).comp (⇑(eval A) U) = (⇑(eval B) U).comp (map ⇑(φ.pow m))

φ induces A^n → B^n and hence ℤ[A^n] →+ ℤ[B^n]
eval A U is the map ℤ[A^m] →+ ℤ[A^n] coming from the universal map
eval B U is the map ℤ[B^m] →+ ℤ[B^n] coming from the universal map
φ induced A^m → B^m and hence ℤ[A^m] →+ ℤ[B^m]

the claim is compositions ℤ[A^m] →+ ℤ[B^n] are the same
we're checking by evaluating them both on elements `as` of A^m


-/

example (A B : Type) [add_comm_group A] [add_comm_group B] (φ : A →+ B) (z : ℤ) (a : A) :
  φ (z • a) = z • φ a := map_int_module_smul φ z a

def universal_map_equiv_functorial_map (m n : ℕ) : universal_map m n ≃+ functorial_map m n :=
{ to_fun := λ U,
  { f := λ A _, by exactI eval A U,
    functorial := λ A _ B _ φ, begin
      resetI,
      ext as,
      rw comp_apply,
      rw comp_apply,
      -- free_abelian_group.map_of should be redefined now map is an add_group_hom not a map
      -- Bhavik says make a dsimp lemma
      change _ = ((eval B) U) ((φ.pow m) <$> (free_abelian_group.of as)),
      rw free_abelian_group.map_of,
      apply free_abelian_group.induction_on U,
      { simp },
      { intro f,
        simp only [basic_universal_map.eval_of, eval_of],
        convert free_abelian_group.map_of _ _,
        ext i,
        rw [pow_eval, add_monoid_hom.map_sum],
        apply finset.sum_congr rfl,
        rintros j -,
        rw [pow_eval, map_int_module_smul] },
      { intros F hF,
        simp only [add_monoid_hom.map_neg, neg_inj, neg_apply, hF] },
      { intros F G hF hG, simp only [hF, hG, add_monoid_hom.map_add, add_apply]}
    end },
  inv_fun := sorry, -- sorrying data
  left_inv := sorry,
  right_inv := sorry,
  map_add' := sorry }

end breen_deligne
