import algebra.homology.chain_complex

import NormedGroup

noncomputable theory

universe variables v u

@[derive category_theory.category]
def system_of_complexes := nnrealᵒᵖ ⥤ (cochain_complex NormedGroup)

namespace system_of_complexes
open opposite category_theory

variables (C : system_of_complexes)

def X (c : nnreal) (i : ℤ) : NormedGroup :=
(C.obj $ op c).X i

def res {c' c : nnreal} {i : ℤ} (h : c ≤ c') :
  C.X c' i ⟶ C.X c i :=
(C.map (has_hom.hom.op ⟨⟨h⟩⟩)).f i

def d {c : nnreal} {i : ℤ} :
  C.X c i ⟶ C.X c (i+1) :=
(C.obj $ op c).d i

/-- Convenience definition:
The identity morphism of an object in the system of complexes
when it is given by different indices that are not
definitionally equal.
-/
def congr {c c' : nnreal} {i i' : ℤ} (hc : c = c') (hi : i = i') :
  C.X c i ⟶ C.X c' i' :=
eq_to_hom $ by { subst hc, subst hi }

/-- Def 9.3 of [Analytic]. -/
def is_bdd_exact_for_bdd_degree_above_idx
  (c₀' : nnreal) (k : nnreal) (m : ℤ) (hk : 1 ≤ k) : Prop :=
∀ c (h : c₀' ≤ c),
∀ i < m,
∀ x : C.X (k * c) (i+1),
∃ y : C.X c i,
∥(C.res (le_mul_of_one_le_left c.2 hk) x) - (C.d y) ∥ ≤ k * ∥C.d x∥

end system_of_complexes
