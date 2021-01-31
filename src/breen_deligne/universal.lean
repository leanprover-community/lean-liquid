-- n©

import breen_deligne.basic

/-!

# Universality of universal maps

A `universal_map m n` in this repo is a formal `ℤ`-linear combination
of `m × n` matrices. In this file we show that this concept is equal
to a collection of maps `ℤ[A^m] → ℤ[A^n]` for each abelian group `A`,
functorial in `A`.

-/

noncomputable theory

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

namespace breen_deligne
open free_abelian_group

structure functorial_map (m n : ℕ) :=
(f (A : Type u) [add_comm_group A] : ℤ[A^m] →+ ℤ[A^n])
(comp (A : Type u) [add_comm_group A] (B : Type u) [add_comm_group B] (φ : A →+ B) :
  (free_abelian_group.map (φ.pow n)).comp (f A) = (f B).comp (map (φ.pow m)))

def universal_map_equiv_functorial_map (m n : ℕ) : universal_map m n ≃ functorial_map m n :=
sorry

end breen_deligne
