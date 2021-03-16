import system_of_complexes.complex
import algebra.homology.exact
/-

# short exact sequences

We develop the notion of short exact sequence, and consider the relation
between a complex of short exact sequences and a short exact sequence
of complexes. Before complexes I guess we do these lawless complexes.
aka `differential_object`s
-/

/-

## Definition `is_short_exact`

It's a true-false statement associated to
a pair `f : A ⟶ B` and `g : B ⟶ C`, so we make
it a `Prop`.

-/

section The_Main_Definition

namespace category_theory
open category_theory.limits
universe uV variables {V : Type uV} [category V] [has_zero_morphisms V] [has_equalizers V] [has_images V]
variables {A B B' C : V} (f : A ⟶ B) (g : B ⟶ C) (g' : B' ⟶ C)
--variable (hₑ : category_theory.exact f g)

class is_short_exact (f : A ⟶ B) (g : B ⟶ C) : Prop :=
(is_exact : exact f g)
(is_mono : mono f)
(is_epi : epi g)

/-!

## A little API for `is_short_exact`

A little API for short exact sequences.

-/
namespace is_short_exact

-- weird remark : if I do not name these instances then type class inference breaks for `glue` below
instance foo [h : is_short_exact f g] : exact f g := h.is_exact
instance bar [h : is_short_exact f g] : mono f := h.is_mono
instance baz [h : is_short_exact f g] : epi g := h.is_epi

theorem w [is_short_exact f g] : f ≫ g = 0 := category_theory.exact.w

-- the bit we have to worry about in topological concrete
-- categories but we can ignore in categories of abelien
-- groups or modules.
theorem glue [is_short_exact f g] : epi (image_to_kernel_map f g exact.w) :=
category_theory.exact.epi

-- do we need anything like `(h : B = B') : is_short_exact' f g' h`? I didn't
-- even try to make it work yet

end is_short_exact

/-

## Short exact sequences of morphisms of lawless complexes

-/

-- let's see how far I get
variable (ι : Type)
variables (P Q R : differential_object ι V)
variable (φ : P ⟶ Q)
variable (ψ : Q ⟶ R)
variable [h : is_short_exact φ ψ]

end category_theory

end The_Main_Definition

/-

## Short exact sequences of morphisms of lawless complexes

-/

variable (ι : Type)
#print differential_object
#check differential_object ι
