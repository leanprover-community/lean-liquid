import algebra.homology.chain_complex

import NormedGroup

noncomputable theory

universe variables v u

@[derive category_theory.category]
def system_of_complexes := nnrealᵒᵖ ⥤ (cochain_complex NormedGroup)

instance nnreal.le_mul_of_one_le_left (k c : nnreal) [hk : fact (1 ≤ k)] :
  fact (c ≤ k * c) :=
le_mul_of_one_le_left c.2 hk

namespace system_of_complexes
open opposite category_theory

variables (C : system_of_complexes)

def X (c : nnreal) (i : ℤ) : NormedGroup :=
(C.obj $ op c).X i

def res {c' c : nnreal} {i : ℤ} [h : fact (c ≤ c')] :
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

/-
Peter Scholze:
(Note that `k` plays a strange double role in Definition 9.3,
quantifying both the depth of restriction and the increase in norm;
somehow it was not necessary to disentangle this for the argument,
so I used one variable for two distinct things.
Only one of them really needs to be `≥1`,
the one parametrizing the depth of restriction.
If one wants to get good estimates at some point,
it may be useful to introduce two parameters here.)

https://leanprover.zulipchat.com/#narrow/stream/266894-liquid/topic/bounded.20exactness/near/220823654
-/

/-- Def 9.3 of [Analytic]. -/
def is_bdd_exact_for_bdd_degree_above_idx
  (k : nnreal) (m : ℤ) (c₀' : nnreal) [hk : fact (1 ≤ k)] : Prop :=
∀ c ≥ c₀', ∀ i < m,
∀ x : C.X (k * c) (i+1),
∃ y : C.X c i, ∥(C.res x) - (C.d y)∥ ≤ k * ∥C.d x∥

end system_of_complexes
