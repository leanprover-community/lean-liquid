import data.real.basic
import algebra.big_operators.basic
import algebra.category.Group.basic
import topology.algebra.infinite_sum
import data.finset.basic
import data.equiv.basic
import analysis.normed_space.basic
import analysis.specific_limits
import data.equiv.basic
import category_theory.Fintype

import Mbar.bounded
import pseudo_normed_group.basic

import for_mathlib.tsum
import for_mathlib.int_norm
import for_mathlib.int_basic

universe u

noncomputable theory
open_locale big_operators nnreal

section definitions

structure c_measures (r : ℝ≥0) (c : ℝ≥0) (S : Type*) (hS : fintype S) :=
(to_fun     : S → ℤ → S → ℤ)
(summable   : ∀ s s', summable (λ n, (↑(to_fun s n s').nat_abs * r ^ n)))
(bdd        : ∀ s s', tsum (λ n, (↑(to_fun s n s').nat_abs * r ^ n)) ≤ c)

structure oc_measures (r : ℝ≥0) (S : Type*) (hS : fintype S) :=
(to_fun      : S → ℤ → S → ℤ)
(summable   : ∀ s s', summable (λ n, (↑(to_fun s n s').nat_abs * r ^ n)))

lemma exists_c (r : ℝ≥0) (S : Type*) (hS : fintype S) (F : oc_measures r S hS) : ∃ (c : ℝ≥0),
  ∀ s s' : S, tsum (λ n, (↑(F.to_fun s n s').nat_abs * r ^ n)) ≤ c := sorry

--should this be a coercion?
def c_measures_to_oc (r : ℝ≥0) (c : ℝ≥0) (S : Type*) (hS : fintype S) :
  c_measures r c S hS → oc_measures r S hS := λ f, ⟨f.to_fun, f.summable⟩

lemma oc_measures_are_c (r : ℝ≥0) (S : Type*) (hS : fintype S) (F : oc_measures r S hS) :
  ∃ (c : ℝ≥0) (f : c_measures r c S hS),
  c_measures_to_oc r c S hS f = F := sorry

--needed?
instance png_oc_measures (r : ℝ≥0) (S : Type*) (hS : fintype S) :
  pseudo_normed_group (oc_measures r S hS) :=
{ to_add_comm_group := sorry,
  filtration := sorry,
  filtration_mono := sorry,
  zero_mem_filtration := sorry,
  neg_mem_filtration := sorry,
  add_mem_filtration := sorry }


variable {α : Type*}

def oc_functor (r : ℝ≥0) : Fintype.{u} ⥤ Ab.{u} :=
{ obj := begin
          intro S,
          have M := png_oc_measures r S.1 S.2,
          have N:= M.to_add_comm_group,
          use N,
          end,
  map := _,
  map_id' := _,
  map_comp' := _ }

end definitions
