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

section punit_stuff

open free_abelian_group

def aux_equiv₁ : ℤ[punit] ≃+ ℤ :=
{ inv_fun := λ n, n • of (punit.star),
  to_fun := free_abelian_group.lift (λ _, (1 : ℤ)),
  left_inv := λ z, free_abelian_group.induction_on z
    (by {dsimp only, rw [add_monoid_hom.map_zero, zero_smul]})
    (λ x, punit.cases_on x (by simp))
    (λ x, punit.cases_on x (by simp))
    (λ x y hx hy, by { simp only [lift.add, add_smul] at *, rw [hx, hy]}),
  right_inv := λ n, by { rw [add_monoid_hom.map_int_module_smul, lift.of], exact gsmul_int_one n},
  map_add' := add_monoid_hom.map_add _ }

def aux_equiv₂ {α β : Type*} (f : α ≃ β) : free_abelian_group α ≃+ free_abelian_group β :=
{ to_fun := free_abelian_group.lift $ free_abelian_group.of ∘ f,
  inv_fun := free_abelian_group.lift $ free_abelian_group.of ∘ f.symm,
  left_inv := begin
    intros x,
    refine free_abelian_group.induction_on x (by simp) (by simp) (by simp) _,
    intros x y h,
    simp [h],
  end,
  right_inv := begin
    intros x,
    refine free_abelian_group.induction_on x (by simp) (by simp) (by simp) _,
    intros x y h,
    simp [h],
  end,
  map_add' := begin
     intros x y,
     simp,
  end }

end punit_stuff

open universal_map
open add_monoid_hom

def universal_map_equiv_functorial_map (m n : ℕ) : universal_map m n ≃+ functorial_map m n :=
{ to_fun := λ U,
  { f := λ A _, by exactI eval A U,
    functorial := λ A _ B _ φ, begin
      -- proof that evaluation of universal maps is functorial for group homomorphisms
      -- We start by unravelling what the question is.
      resetI,
      ext as,
      rw [comp_apply, comp_apply],
      -- free_abelian_group.map_of should be redefined now map is an add_group_hom not a map?
      -- Bhavik says make a dsimp lemma, I say make map_of'
      change _ = ((eval B) U) ((φ.pow m) <$> (free_abelian_group.of as)),
      rw free_abelian_group.map_of,
      --  We need to prove that for all `as : A^m`, evaluating U then mapping with φ
      -- is the same as applying φ and then evaluating U on the corresponding element of
      -- ℤ[B^m].
      -- By linearity, we can assume that `U` is a basic universal map `f`.
      apply free_abelian_group.induction_on U,
      { simp },
      { intro f,
        -- Here is the proof for basic universal maps.
        simp only [basic_universal_map.eval_of, eval_of],
        -- We use the universal property
        convert free_abelian_group.map_of _ _,
        -- which boils the question down to checking that φ : A^n → B^n and φ : A^m → B^m
        -- commutes with the matrix action A^m → A^n
        ext i,
        -- and this just boils down to trivialities
        rw [pow_eval, add_monoid_hom.map_sum],
        apply finset.sum_congr rfl,
        rintros j -,
        rw [pow_eval, map_int_module_smul] },
        -- the rest is just checking that the question about universal maps was linear
        -- so the reduction to the basic case was OK.
      { intros F hF,
        simp only [add_monoid_hom.map_neg, neg_inj, neg_apply, hF] },
      { intros F G hF hG, simp only [hF, hG, add_monoid_hom.map_add, add_apply]}
    end },
  inv_fun := λ F, free_abelian_group.lift
    (λ x, free_abelian_group.of
      (λ i j, (aux_equiv₁ ((x : (ℤ[punit] ^ m) ^ n) i j)) : basic_universal_map m n))
    (F.f
      (free_abelian_group (punit)^m)
      (free_abelian_group.of (λ i j, if i = j then free_abelian_group.of punit.star else 0))),
    left_inv := begin
      intro u,
      apply free_abelian_group.induction_on u,
      { simp },
      { intro b,
        simp only [free_abelian_group.lift.of, basic_universal_map.eval_of, eval_of],
        congr',
        ext i j,
        sorry -- I've done a goal like this above
      },
      { simp },
      { intros u v hu hv,
        simp * at * }
    end,
  right_inv := sorry, -- no idea how hard this will be
  map_add' := sorry -- should be no problem
  }

end breen_deligne
