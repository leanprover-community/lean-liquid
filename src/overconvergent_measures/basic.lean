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
import pseudo_normed_group.category

import for_mathlib.tsum
import for_mathlib.int_norm
import for_mathlib.int_basic

universe u

noncomputable theory
open_locale big_operators nnreal

section definitions

/-
structure c_measures (r : ℝ≥0) (c : ℝ≥0) (S : Fintype) :=
(to_fun     : S → ℤ → ℤ)
(summable   : ∀ s, summable (λ n, (∥ to_fun s n ∥₊ * r ^ n)))
(bdd        : ∀ s, tsum (λ n, (∥ to_fun s n ∥₊ * r ^ n)) ≤ c)
-/

structure oc_measures (r : ℝ≥0) (S : Fintype) :=
(to_fun     : S → ℤ → ℤ)
(summable   : ∀ s, summable (λ n, ∥ to_fun s n ∥₊ * r ^ n))

def oc_measures' (r : ℝ≥0) (S : Fintype) : add_subgroup (S → ℤ → ℤ) :=
{ carrier := { F | ∀ s, summable (λ n, ∥ F s n ∥₊ * r ^ n) },
  zero_mem' := begin
    dsimp,
    intro s,
    simp,
    exact summable_zero,
  end,
  add_mem' := begin
    intros F G hF hG,
    dsimp at *,
    intros s,
    specialize hF s,
    specialize hG s,
    have : ∀ n : ℤ, ∥ F s n + G s n∥₊ * r ^ n ≤ ∥ F s n ∥₊ * r ^ n + ∥ G s n ∥₊ * r ^ n, sorry,
    --apply summable_of_nonneg_of_le _ this, :-/
    sorry,
  end,
  neg_mem' := begin
    dsimp,
    intro s,
    simp,
  end }

instance {r S} : has_coe_to_fun (oc_measures r S) :=
⟨λ F, S → ℤ → ℤ, λ F, F.to_fun⟩

@[ext]
lemma oc_measures.ext {r S} (F G : oc_measures r S) : (F : S → ℤ → ℤ) = G → F = G :=
by { intros h, cases F, cases G, simpa }

instance {r S} : add_comm_group (oc_measures r S) := sorry

def filtration (r c : ℝ≥0) (S : Fintype) : set (oc_measures r S) :=
{ F | ∀ s, ∑' n, ∥ F s n ∥₊ ≤ c }

lemma exists_c (r : ℝ≥0) (S : Fintype) (F : oc_measures r S) : ∃ (c : ℝ≥0),
  ∀ s : S, ∑' n, ∥ F s n ∥₊ ≤ c :=
begin
  use ∑ s, ∑' n, ∥ F s n ∥₊,
  intro s,
  sorry,
end

/-
--should this be a coercion?
def c_measures_to_oc (r : ℝ≥0) (c : ℝ≥0) (S : Type*) (hS : fintype S) :
  c_measures r c S hS → oc_measures r S hS := λ f, ⟨f.to_fun, f.summable⟩

lemma oc_measures_are_c (r : ℝ≥0) (S : Type*) (hS : fintype S) (F : oc_measures r S hS) :
  ∃ (c : ℝ≥0) (f : c_measures r c S hS),
  c_measures_to_oc r c S hS f = F := sorry
-/

--needed?
instance png_oc_measures (r : ℝ≥0) (S : Fintype) :
 profinitely_filtered_pseudo_normed_group (oc_measures r S) := sorry

variable {α : Type*}

def oc_functor (r : ℝ≥0) : Fintype.{u} ⥤ ProFiltPseuNormGrp.{u} :=
{ obj := λ S, ProFiltPseuNormGrp.of $ oc_measures r S,
  map := λ S T f,
  { to_fun := _,
    map_zero' := _,
    map_add' := _,
    bound' := _,
    continuous' := _ },
  map_id' := _,
  map_comp' := _ }

end definitions
