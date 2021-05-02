import for_mathlib.grading
import ring_theory.noetherian -- for the lemma we need for Gordan
import ring_theory.finiteness

/-!

# The `zero_component_subring` of a commutative graded ring

Some definitions and lemmas about commutative graded rings, graded by `add_subgroup`s which
are indexed by an `add_monoid`. We are mostly concerned with the relationship between the
ring `R` and the `zero_component_subring` `R₀`. All of this stuff will also pretty clearly work
for gradings indexed by `monoid`s. Most of it will probably work in the non-commutative case,
sometimes under the extra assumption that `R₀` is commutative. Most of it will work for `semirings`
graded by `add_submonoid`s but I find it difficult to reuse `semiring` results to get `ring`
results.

## Main definitions

If `R` is a commutative ring graded by `add_subgroup`s Gᵢ indexed by an `add_monoid` A,
then

* `zero_piece_subring R Gᵢ` := `Gᵢ 0` or `R₀` is a subring and `R` is an algebra for `R₀` and hence
    an `R₀`-module;
* If `a : A` then `Gᵢ a` is a submodule.

## Main theorems

* Given a `Gᵢ 0`-submodule of `Gᵢ a`, pushing forward to an ideal of `R` and then pulling back
    is the identity function.
* Hence if `R` is a Noetherian ring then `Gᵢ a` are all Noetherian `R₀`-modules.

-/

/-

## preparations

-/

-- move this, if it's not there already
def subring.incl (R : Type) [comm_ring R] (A B : subring R) (h : A ≤ B) : A →+* B :=
{ to_fun := λ a, ⟨a.1, h a.2⟩,
  map_zero' := rfl,
  map_add' := λ _ _, rfl,
  map_one' := rfl,
  map_mul' := λ _ _, rfl }

namespace direct_sum

namespace has_add_subgroup_decomposition

section ring

variables {A : Type*} [decidable_eq A] [add_monoid A]
  (R : Type*) [ring R]
  (Gᵢ : A → add_subgroup R) [has_add_subgroup_decomposition Gᵢ] [add_subgroup.is_gmonoid Gᵢ]

-- would love to deduce this from `subsemiring_of_add_submonoid` but it's all too much
-- for `convert` because an external direct sum of `Gᵢ i` is syntactically different to
-- an external direct sum of `(Gᵢ i).to_add_submonoid` and this can cause problems.
def subring_of_add_subgroup
    (S : add_submonoid A) : subring R :=
 { carrier := {r : R | ∀ ⦃a : A⦄, a ∉ S → add_subgroup_decomposition Gᵢ r a = 0 },
   zero_mem' := λ n _, by { rw (add_subgroup_decomposition Gᵢ).map_zero, refl },
   add_mem' := λ a b ha hb n hn, by
   { rw [(add_subgroup_decomposition Gᵢ).map_add, dfinsupp.add_apply, ha hn, hb hn, zero_add] },
   neg_mem' := λ a ha n hn, by
   { rw [(add_subgroup_decomposition Gᵢ).map_neg],
     convert dfinsupp.neg_apply _ n,
     rw ha hn,
     simp },
    one_mem' := λ n hn, (mem_piece_iff_single_support 1 0).1
     (add_subgroup.is_gmonoid.grading_one) (λ h, hn $ by { rw h, exact S.zero_mem }),
   mul_mem' := λ a b,
    let a' := add_subgroup_decomposition Gᵢ a in
    let b' := add_subgroup_decomposition Gᵢ b in
    λ (ha : ∀ ai ∉ S, a' ai = 0) (hb : ∀ bi ∉ S, b' bi = 0) n hn, begin
      change ((add_subgroup_decomposition_ring_equiv Gᵢ) (a * b)) n = 0,
      rw ring_equiv.map_mul,
      change (a' * b') n = 0,
      classical,
      rw has_add_submonoid_decomposition.direct_sum.mul_apply,
      apply dfinsupp.sum_eq_zero,
      intros ai hai,
      apply dfinsupp.sum_eq_zero,
      intros bi hbi,
      apply dif_neg,
      rintro rfl,
      obtain (hna | hnb) := S.not_mem_or_of_add_not_mem hn,
      exact hai (ha _ hna),
      exact hbi (hb _ hnb),
    end,
 }

-- has better definitional properties than `subring_of_add_subgroup A R Gᵢ ⊥
def zero_component_subring : subring R :=
{ one_mem' := add_subgroup.is_gmonoid.grading_one,
  mul_mem' := λ r s, begin
    suffices : r ∈ Gᵢ 0 → s ∈ Gᵢ 0 → r * s ∈ Gᵢ (0 + 0),
      simpa,
    exact add_subgroup.is_gmonoid.grading_mul,
  end,
  ..Gᵢ 0
}

-- instance : ring (zero_component_subring R Gᵢ) := infer_instance

end ring

-- in the commutative case we can go further because R is then an R₀-module

section comm_ring

variables {A : Type*} [decidable_eq A] [add_monoid A]
  (R : Type*) [comm_ring R]
  (Gᵢ : A → add_subgroup R) [has_add_subgroup_decomposition Gᵢ] [add_subgroup.is_gmonoid Gᵢ]

def component_submodule_for_zero_component_subring (a : A) :
  submodule (zero_component_subring R Gᵢ) R :=
{ carrier := Gᵢ a,
  zero_mem' := (Gᵢ a).zero_mem,
  add_mem' := λ _ _, (Gᵢ a).add_mem,
  smul_mem' := begin
    rintro ⟨c, (hc : c ∈ Gᵢ 0)⟩ x (hx : x ∈ Gᵢ a),
    change c * x ∈ Gᵢ a,
    convert add_subgroup.is_gmonoid.grading_mul hc hx,
    rw zero_add,
  end }


namespace component_submodule -- some technical lemmas

def map (a : A) (M : submodule
  (zero_component_subring R Gᵢ) (component_submodule_for_zero_component_subring R Gᵢ a)) :
  submodule R R := submodule.span R {r : R | ∃ m : M, r = m.1}

def res (a : A) (I : submodule R R) : submodule (zero_component_subring R Gᵢ) R :=
sorry
--{! !} doesn't work for me??

theorem comap (a : A) (I : submodule R R) : submodule
  (zero_component_subring R Gᵢ) (component_submodule_for_zero_component_subring R Gᵢ a) :=
sorry

end component_submodule

/--
Pushing forward an R₀-submodule of Rₐ to an R-submodule of R, and then intersecting with R₀
again gives you the submodule you started with.
-/

theorem component_submodule_noetherian {R : Type*} [comm_ring R] [is_noetherian_ring R]
  {A : Type*} [add_monoid A] [decidable_eq A]
  (Gᵢ : A → add_subgroup R) [has_add_subgroup_decomposition Gᵢ] [add_subgroup.is_gmonoid Gᵢ]
  (a : A) : is_noetherian (zero_component_subring R Gᵢ)
    (component_submodule_for_zero_component_subring R Gᵢ a) :=
begin
  sorry
end

end comm_ring

end has_add_subgroup_decomposition

end direct_sum
