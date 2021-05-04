import data.equiv.basic

-- this is mathlib PR: #7458

@[simps {fully_applied := ff}]
def equiv.curry (α β γ : Type*) :
  (α × β → γ) ≃ (α → β → γ) :=
{ to_fun := function.curry,
  inv_fun := function.uncurry,
  left_inv := function.uncurry_curry,
  right_inv := function.curry_uncurry }
