import algebra.homology.chain_complex

import normed_group.NormedGroup
import algebra.ordered_group
import facts
import for_mathlib.category_theory

universe variables v u
noncomputable theory
open opposite category_theory
open_locale nnreal

/-!
# Systems of complexes of normed abelian groups

In this file we define systems of complexes of normed abelian groups,
along the lines of Definition 9.3 of [Analytic].

## Main declarations

* `system_of_complexes`: a system of complexes of normed abelian groups.
* `is_bdd_exact_for_bdd_degree_above_idx`: an exactness criterion for such systems,
    requiring a suitable interplay between the norms and the algebraic properties of the system.
* `admissible`: such a system is *admissible* if all maps that occur in the system
    are norm-nonincreasing.
-/

-- TODO: at some point we can abstract the following definition over `NormedGroup` and `ℝ≥0`.
-- But I don't think that is relevant for this project.

/-- A system of complexes of normed abelian groups, indexed by `ℝ≥0`.
See also Definition 9.3 of [Analytic].

Implementation detail: `cochain_complex` assumes that the complex is indexed by `ℤ`,
whereas we are interested in complexes indexed by `ℕ`.
We therefore set all objects indexed by negative integers to `0`, in our use case. -/
@[derive category_theory.category]
def system_of_complexes : Type* := ℝ≥0ᵒᵖ ⥤ (cochain_complex NormedGroup)

variables {M M' N : system_of_complexes.{u}} (f : M ⟶ M') (g : M' ⟶ N)

/-- `C.X c i` is the object $C_c^i$ in a system of complexes `C`. -/
def system_of_complexes.X (C : system_of_complexes.{u}) (c : ℝ≥0) (i : ℤ) : NormedGroup :=
(C.obj $ op c).X i

/-- `f.apply c i` is application of the natural transformation `f`: $f_c^i : M_c^i ⟶ N_c^i$. -/
def category_theory.has_hom.hom.apply (f : M ⟶ N) {c : ℝ≥0} {i : ℤ} : M.X c i ⟶ N.X c i :=
(f.app (op c)).f i

/-- `f.apply c i` is application of the natural isomorphism `f`: $f_c^i : M_c^i ≅ N_c^i$. -/
def category_theory.iso.apply (f : M ≅ N) {c : ℝ≥0} {i : ℤ} : M.X c i ≅ N.X c i :=
pi.iso_app (differential_object.iso_app $ f.app $ op c) i

namespace system_of_complexes

variables (C C₁ C₂ : system_of_complexes.{u})

/-- `C.res` is the restriction map `C.X c' i ⟶ C.X c i` for a system of complexes `C`,
and nonnegative reals `c ≤ c'`. -/
def res {C : system_of_complexes} {c' c : ℝ≥0} {i : ℤ} [h : fact (c ≤ c')] : C.X c' i ⟶ C.X c i :=
(C.map (hom_of_le h).op).f i

variables {c₁ c₂ c₃ : ℝ≥0} (i : ℤ)

@[simp] lemma res_comp_res (h₁ : fact (c₂ ≤ c₁)) (h₂ : fact (c₃ ≤ c₂)) :
  @res C _ _ i h₁ ≫ @res C _ _ i h₂ = @res C _ _ i (le_trans h₂ h₁) :=
begin
  have := (category_theory.functor.map_comp C (hom_of_le h₁).op (hom_of_le h₂).op),
  rw [← op_comp] at this,
  delta res,
  erw this,
  refl,
end

@[simp] lemma res_res (h₁ : fact (c₂ ≤ c₁)) (h₂ : fact (c₃ ≤ c₂)) (x : C.X c₁ i) :
  @res C _ _ i h₂ (@res C _ _ i h₁ x) = @res C _ _ i (le_trans h₂ h₁) x :=
by { rw ← (C.res_comp_res i h₁ h₂), refl }

/-- `C.d` is the differential `C.X c i ⟶ C.X c (i+1)` for a system of complexes `C`. -/
def d {C : system_of_complexes} {c : ℝ≥0} {i : ℤ} :
  C.X c i ⟶ C.X c (i+1) :=
(C.obj $ op c).d i

lemma d_comp_res (h : fact (c₂ ≤ c₁)) :
  @d C c₁ i ≫ @res C _ _ _ h = @res C _ _ i _ ≫ @d C c₂ i :=
homological_complex.comm_at (C.map (hom_of_le h).op) i

lemma d_res (h : fact (c₂ ≤ c₁)) (x) :
  @d C c₂ i (@res C _ _ i _ x) = @res C _ _ _ h (@d C c₁ i x) :=
show (@res C _ _ i _ ≫ @d C c₂ i) x = (@d C c₁ i ≫ @res C _ _ _ h) x,
by rw d_comp_res

section iso

variables (ϕ : M ≅ N) (c : ℝ≥0) (i)

lemma apply_hom_eq_hom_apply : (ϕ.apply.hom : M.X c i ⟶ N.X c i) = ϕ.hom.apply := rfl

lemma apply_inv_eq_inv_apply : (ϕ.apply.inv : N.X c i ⟶ M.X c i) = ϕ.inv.apply := rfl

@[simp] lemma hom_apply_comp_inv_apply :
  (ϕ.hom.apply : M.X c i ⟶ N.X c i) ≫ ϕ.inv.apply = 𝟙 _ :=
by rw [← apply_hom_eq_hom_apply, ← apply_inv_eq_inv_apply, iso.hom_inv_id]

@[simp] lemma inv_apply_comp_hom_apply :
  (ϕ.inv.apply : N.X c i ⟶ M.X c i) ≫ ϕ.hom.apply = 𝟙 _ :=
by rw [← apply_hom_eq_hom_apply, ← apply_inv_eq_inv_apply, iso.inv_hom_id]

@[simp] lemma inv_apply_hom_apply (x : M.X c i) :
  ϕ.inv.apply (ϕ.hom.apply x) = x :=
show ((ϕ.hom.apply : M.X c i ⟶ N.X c i) ≫ ϕ.inv.apply) x = x,
by simp only [hom_apply_comp_inv_apply, coe_id, id.def]

@[simp] lemma hom_apply_inv_apply (x : N.X c i) :
  ϕ.hom.apply (ϕ.inv.apply x) = x :=
show ((ϕ.inv.apply : N.X c i ⟶ M.X c i) ≫ ϕ.hom.apply) x = x,
by simp only [inv_apply_comp_hom_apply, coe_id, id.def]

end iso

/-- Convenience definition:
The identity morphism of an object in the system of complexes
when it is given by different indices that are not
definitionally equal. -/
def congr {c c' : ℝ≥0} {i i' : ℤ} (hc : c = c') (hi : i = i') :
  C.X c i ⟶ C.X c' i' :=
eq_to_hom $ by { subst hc, subst hi }

variables (M M' N)

lemma d_apply (f : M ⟶ N) {c : ℝ≥0} {i : ℤ} (m : M.X c i) :
  d (f.apply m) = f.apply (d m) :=
begin
  have h : ((M.obj (op c)).d i ≫ (f.app (op c)).f (i + 1)) m =
    (f.app (op c)).f (i + 1) ((M.obj (op c)).d i m),
  { exact coe_comp ((M.obj (op c)).d i) ((f.app (op c)).f (i + 1)) m },
  rwa [homological_complex.comm_at (f.app (op c)) i] at h,
end

lemma res_comp_apply (f : M ⟶ N) (c c' : ℝ≥0) [h : fact (c ≤ c')] (i : ℤ) :
  @res M c' c i _ ≫ f.apply = f.apply ≫ res :=
begin
  have step1 := f.naturality (hom_of_le h).op,
  have step2 := congr_arg differential_object.hom.f step1,
  exact congr_fun step2 i
end

lemma res_apply (f : M ⟶ N) (c c' : ℝ≥0) [h : fact (c ≤ c')] {i : ℤ} (m : M.X c' i) :
  @res N c' c _ _ (f.apply m) = f.apply (res m) :=
begin
  show (f.apply ≫ (@res N c' c _ _)) m = (@res M c' c _ _ ≫ (f.apply)) m,
  rw res_comp_apply
end

/-- A system of complexes is *admissible*
if all the differentials and restriction maps are norm-nonincreasing.

See Definition 9.3 of [Analytic]. -/
structure admissible (C : system_of_complexes) : Prop :=
(d_norm_noninc : ∀ c i, (d : C.X c i ⟶ C.X c (i+1)).norm_noninc)
(res_norm_noninc : ∀ c' c i h, (@res C c' c i h).norm_noninc)

/-- `is_bdd_exact_for_bdd_degree_above_idx k m c₀` is a predicate on systems of complexes.

A system of complexes `C` is *`≤ k`-exact in degrees `≤ m` for `c ≥ c₀`*
if the following condition is satisfied:
For all `c ≥ c₀` and all `x : C.X (k * c) i` with `i ≤ m` there is some `y : C.X c (i-1)`
(which is defined to be `0` when `i = 0`) such that `∥(C.res x) - (C.d y)∥ ≤ k * ∥C.d x∥`.

See Definition 9.3 of [Analytic].

Implementation details:
* Because our chain complexes are indexed by `ℤ` instead of `ℕ`,
  and we make sure that objects indexed by negative integers are `0`,
  we automatically take care of the parenthetical condition about `i = 0`.
* The original text bounds `i` as `i ≤ m`, and then requires `y : C.X c (i-1)`.
  We change this to `i < m` and `y : C.X c i`, because this has better definitional properties.
  (This is a hack around an inconvenience known as dependent type theory hell.) -/
def is_bdd_exact_for_bdd_degree_above_idx
  (k K : ℝ≥0) (m : ℤ) [hk : fact (1 ≤ k)] (c₀ : ℝ≥0) : Prop :=
∀ c ≥ c₀, ∀ i < m,
∀ x : C.X (k * c) (i+1),
∃ y : C.X c i, ∥res x - d y∥ ≤ K * ∥d x∥

/-- Weak version of `is_bdd_exact_for_bdd_degree_above_idx`. -/
def is_weak_bdd_exact_for_bdd_degree_above_idx
  (k K : ℝ≥0) (m : ℤ) [hk : fact (1 ≤ k)] (c₀ : ℝ≥0) : Prop :=
∀ c ≥ c₀, ∀ i < m,
∀ x : C.X (k * c) (i+1),
∀ ε > 0, ∃ y : C.X c i, ∥res x - d y∥ ≤ K * ∥d x∥ + ε

--TODO: equivalence between weak and strong for complete spaces

namespace is_bdd_exact_for_bdd_degree_above_idx

variables {C C₁ C₂}
variables {k k' K K' : ℝ≥0} {m m' : ℤ} {c₀ c₀' : ℝ≥0} [fact (1 ≤ k)] [fact (1 ≤ k')]

lemma of_le (hC : C.is_bdd_exact_for_bdd_degree_above_idx k K m c₀)
  (hC_adm : C.admissible) (hk : k ≤ k') (hK : K ≤ K') (hm : m' ≤ m) (hc₀ : c₀ ≤ c₀') :
  C.is_bdd_exact_for_bdd_degree_above_idx k' K' m' c₀' :=
begin
  intros c hc i hi x,
  haveI : fact (k ≤ k') := hk,
  obtain ⟨y, hy⟩ := hC c (hc₀.trans hc) i (lt_of_lt_of_le hi hm) (res x),
  use y,
  simp only [res_res] at hy,
  refine le_trans hy _,
  rw d_res,
  exact mul_le_mul hK (hC_adm.res_norm_noninc _ _ _ _ (d x)) (norm_nonneg _) ((zero_le K).trans hK)
end

lemma of_iso (h : C₁.is_bdd_exact_for_bdd_degree_above_idx k K m c₀) (f : C₁ ≅ C₂)
  (hf : ∀ c i, (f.hom.apply : C₁.X c i ⟶ C₂.X c i).is_strict) :
  C₂.is_bdd_exact_for_bdd_degree_above_idx k K m c₀ :=
begin
  intros c hc i hi x,
  obtain ⟨y, hy⟩ := h c hc i hi (f.inv.apply x),
  refine ⟨f.hom.apply y, _⟩,
  calc  ∥res x - d (f.hom.apply y)∥
      = ∥res x - f.hom.apply (d y)∥ : by rw d_apply
  ... = ∥f.hom.apply (f.inv.apply (res x)) - f.hom.apply (d y)∥ : by rw hom_apply_inv_apply
  ... = ∥f.hom.apply (f.inv.apply (res x) - d y)∥ : by rw f.hom.apply.map_sub
  ... = ∥f.inv.apply (res x) - d y∥ : hf _ _ _
  ... = ∥res (f.inv.apply x) - d y∥ : by rw res_apply
  ... ≤ K * ∥d (f.inv.apply x)∥ : hy
  ... = K * ∥d x∥ : congr_arg _ _,
  calc  ∥d (f.inv.apply x)∥
      = ∥f.inv.apply (d x)∥ : by rw d_apply
  ... = ∥f.hom.apply (f.inv.apply (d x))∥ : (hf _ _ _).symm
  ... = ∥d x∥ : by rw hom_apply_inv_apply
end

end is_bdd_exact_for_bdd_degree_above_idx

section quotient

open normed_group_hom

variables {M M'}

/-- The quotient of a system of complexes. -/
def is_quotient (f : M ⟶ M') : Prop :=
∀ c i, normed_group_hom.is_quotient (f.apply : M.X c i ⟶ M'.X c i)

/-- The quotient of an admissible system of complexes is admissible. -/
lemma admissible_of_quotient {f : M ⟶ M'} (hquot : is_quotient f) (hadm : M.admissible) :
  M'.admissible :=
begin
  split,
  { intros c i m',
    refine le_of_forall_pos_le_add _,
    intros ε hε,
    obtain ⟨m, hm⟩ := quotient_norm_lift (hquot _ _) hε m',
    rw [← hm.1, d_apply],
    calc ∥f.apply (d m)∥ ≤ ∥d m∥ : quotient_norm_le (hquot _ _) _
      ... ≤ ∥m∥ : hadm.d_norm_noninc _ _ m
      ... ≤ ∥m'∥ + ε : le_of_lt hm.2
      ... = ∥f.apply m∥ + ε : by rw [hm.1] },
  { intros c' c i hc m',
    letI h := hc,
    refine le_of_forall_pos_le_add _,
    intros ε hε,
    obtain ⟨m, hm⟩ := quotient_norm_lift (hquot _ _) hε m',
    rw [← hm.1, res_apply],
    calc ∥f.apply (res m)∥ ≤ ∥res m∥ : quotient_norm_le (hquot _ _) _
      ... ≤ ∥m∥ : hadm.res_norm_noninc c' c _ hc m
      ... ≤ ∥m'∥ + ε : le_of_lt hm.2
      ... = ∥f.apply m∥ + ε : by rw [hm.1] }
end

end quotient

end system_of_complexes

-- #lint- only unused_arguments def_lemma doc_blame
