-- import algebra.homology.chain_complex

import for_mathlib.normed_group_quotient
import system_of_complexes.complex

import normed_group.NormedGroup
import algebra.ordered_group
import facts

import tactic.gptf

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
* `is_bounded_exact`: an exactness criterion for such systems,
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
def system_of_complexes : Type* := ℝ≥0ᵒᵖ ⥤ (cochain_complex ℤ NormedGroup)

-- instance : has_shift system_of_complexes := has_shift.mk $ (shift _).congr_right

variables {M M' N : system_of_complexes.{u}} (f : M ⟶ M') (g : M' ⟶ N)

instance : has_coe_to_fun system_of_complexes :=
⟨λ C, ℝ≥0 → ℤ → NormedGroup, λ C c i, (C.obj $ op c).X i⟩

/-- `f.apply c i` is application of the natural transformation `f`: $f_c^i : M_c^i ⟶ N_c^i$. -/
def category_theory.has_hom.hom.apply (f : M ⟶ N) {c : ℝ≥0} {i : ℤ} : M c i ⟶ N c i :=
(f.app (op c)).f i

instance hom_to_fun : has_coe_to_fun (M ⟶ N) :=
⟨λ f, Π {c : ℝ≥0} {i : ℤ}, M c i → N c i, λ f {c} {i} x, f.apply x⟩

lemma system_of_complexes.map_sub (f : M ⟶ N) {c i} (m m' : M c i) : f (m-m') = f m - f m' :=
normed_group_hom.map_sub _ _ _

/-- `f.apply c i` is application of the natural isomorphism `f`: $f_c^i : M_c^i ≅ N_c^i$. -/
def category_theory.iso.apply (f : M ≅ N) {c : ℝ≥0} {i : ℤ} : M c i ≅ N c i :=
differential_object.iso_app (f.app (op c)) i

namespace system_of_complexes

variables (C C₁ C₂ : system_of_complexes.{u})

/-- `res` is the restriction map `C c' i ⟶ C c i` for a system of complexes `C`,
and nonnegative reals `c ≤ c'`. -/
def res {C : system_of_complexes} {c' c : ℝ≥0} {i : ℤ} [h : fact (c ≤ c')] : C c' i ⟶ C c i :=
(C.map (hom_of_le h).op).f i

variables {c₁ c₂ c₃ : ℝ≥0} (i j k : ℤ)

@[simp] lemma res_comp_res (h₁ : fact (c₂ ≤ c₁)) (h₂ : fact (c₃ ≤ c₂)) :
  @res C _ _ i h₁ ≫ @res C _ _ i h₂ = @res C _ _ i (le_trans h₂ h₁) :=
begin
  have := (category_theory.functor.map_comp C (hom_of_le h₁).op (hom_of_le h₂).op),
  rw [← op_comp] at this,
  delta res,
  erw this,
  refl,
end

@[simp] lemma res_res (h₁ : fact (c₂ ≤ c₁)) (h₂ : fact (c₃ ≤ c₂)) (x : C c₁ i) :
  @res C _ _ i h₂ (@res C _ _ i h₁ x) = @res C _ _ i (le_trans h₂ h₁) x :=
by { rw ← (C.res_comp_res i h₁ h₂), refl }

/-- `C.d` is the differential `C c i ⟶ C c (i+1)` for a system of complexes `C`. -/
def d (C : system_of_complexes) {c : ℝ≥0} (i j : ℤ) : C c i ⟶ C c j :=
(C.obj $ op c).d i j

lemma d_comp_d (c : ℝ≥0) (i j k : ℤ) : C.d i j ≫ (C.d j k : C c j ⟶ _) = 0 :=
(C.obj $ op c).d_comp_d _ _ _

@[simp] lemma d_d (c : ℝ≥0) (i j k : ℤ) (x : C c i) :
  C.d j k (C.d i j x) = 0 :=
show ((C.d i j) ≫ C.d j k) x = 0, by { rw d_comp_d, refl }

lemma d_comp_res (h : fact (c₂ ≤ c₁)) :
  C.d i j ≫ @res C _ _ _ h = @res C _ _ _ _ ≫ C.d i j :=
(C.map (hom_of_le h).op).comm _ _

lemma d_res (h : fact (c₂ ≤ c₁)) (x) :
  C.d i j (@res C _ _ _ _ x) = @res C _ _ _ h (C.d i j x) :=
show (@res C _ _ _ _ ≫ C.d i j) x = (C.d i j ≫ @res C _ _ _ h) x,
by rw d_comp_res

section iso

variables (ϕ : M ≅ N) (c : ℝ≥0) (i)

lemma apply_hom_eq_hom_apply : (ϕ.apply.hom : M c i ⟶ N c i) = ϕ.hom.apply := rfl

lemma apply_inv_eq_inv_apply : (ϕ.apply.inv : N c i ⟶ M c i) = ϕ.inv.apply := rfl

@[simp] lemma hom_apply_comp_inv_apply :
  (ϕ.hom.apply : M c i ⟶ N c i) ≫ ϕ.inv.apply = 𝟙 _ :=
by rw [← apply_hom_eq_hom_apply, ← apply_inv_eq_inv_apply, iso.hom_inv_id]

@[simp] lemma inv_apply_comp_hom_apply :
  (ϕ.inv.apply : N c i ⟶ M c i) ≫ ϕ.hom.apply = 𝟙 _ :=
by rw [← apply_hom_eq_hom_apply, ← apply_inv_eq_inv_apply, iso.inv_hom_id]

@[simp] lemma inv_apply_hom_apply (x : M c i) :
  ϕ.inv.apply (ϕ.hom.apply x) = x :=
show ((ϕ.hom.apply : M c i ⟶ N c i) ≫ ϕ.inv.apply) x = x,
by simp only [hom_apply_comp_inv_apply, coe_id, id.def]

@[simp] lemma hom_apply_inv_apply (x : N c i) :
  ϕ.hom (ϕ.inv x) = x :=
show ((ϕ.inv.apply : N c i ⟶ M c i) ≫ ϕ.hom.apply) x = x,
by simp only [inv_apply_comp_hom_apply, coe_id, id.def]

end iso

/-- Convenience definition:
The identity morphism of an object in the system of complexes
when it is given by different indices that are not
definitionally equal. -/
def congr {c c' : ℝ≥0} {i i' : ℤ} (hc : c = c') (hi : i = i') :
  C c i ⟶ C c' i' :=
eq_to_hom $ by { subst hc, subst hi }

variables (M M' N)

lemma d_apply (f : M ⟶ N) {c : ℝ≥0} {i j : ℤ} (m : M c i) :
  N.d i j (f m) = f (M.d i j m) :=
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

lemma res_apply (f : M ⟶ N) (c c' : ℝ≥0) [h : fact (c ≤ c')] {i : ℤ} (m : M c' i) :
  @res N c' c _ _ (f m) = f (res m) :=
begin
  show (f.apply ≫ (@res N c' c _ _)) m = (@res M c' c _ _ ≫ (f.apply)) m,
  rw res_comp_apply
end

/-- A system of complexes is *admissible*
if all the differentials and restriction maps are norm-nonincreasing.

See Definition 9.3 of [Analytic]. -/
structure admissible (C : system_of_complexes) : Prop :=
(d_norm_noninc : ∀ c i, (d : C c i ⟶ C c (i+1)).norm_noninc)
(res_norm_noninc : ∀ c' c i h, (@res C c' c i h).norm_noninc)

/-- `is_bounded_exact k K m c₀` is a predicate on systems of complexes.

A system of complexes `C` is `(k,K)`-exact in degrees `≤ m` for `c ≥ c₀`*
if the following condition is satisfied:
For all `c ≥ c₀` and all `x : C (k * c) i` with `i ≤ m` there is some `y : C c (i-1)`
(which is defined to be `0` when `i = 0`) such that `∥(C.res x) - (C.d y)∥ ≤ K * ∥C.d x∥`.

See Definition 9.3 of [Analytic] (which coalesces the roles of `k` and `K`).

Implementation details:
* Because our chain complexes are indexed by `ℤ` instead of `ℕ`,
  and we make sure that objects indexed by negative integers are `0`,
  we automatically take care of the parenthetical condition about `i = 0`.
* The original text bounds `i` as `i ≤ m`, and then requires `y : C c (i-1)`.
  We change this to `i < m` and `y : C c i`, because this has better definitional properties.
  (This is a hack around an inconvenience known as dependent type theory hell.) -/
def is_bounded_exact
  (k K : ℝ≥0) (m : ℤ) [hk : fact (1 ≤ k)] (c₀ : ℝ≥0) : Prop :=
∀ c ≥ c₀, ∀ i < m,
∀ x : C (k * c) (i+1),
∃ y : C c i, ∥res x - d y∥ ≤ K * ∥d x∥

/-- Weak version of `is_bounded_exact`. -/
def is_weak_bounded_exact
  (k K : ℝ≥0) (m : ℤ) [hk : fact (1 ≤ k)] (c₀ : ℝ≥0) : Prop :=
∀ c ≥ c₀, ∀ i < m,
∀ x : C (k * c) (i+1),
∀ ε > 0, ∃ y : C c i, ∥res x - d y∥ ≤ K * ∥d x∥ + ε

namespace is_weak_bounded_exact

variables {C C₁ C₂}
variables {k k' K K' : ℝ≥0} {m m' : ℤ} {c₀ c₀' : ℝ≥0} [fact (1 ≤ k)] [fact (1 ≤ k')]

lemma of_le (hC : C.is_weak_bounded_exact k K m c₀)
  (hC_adm : C.admissible) (hk : k ≤ k') (hK : K ≤ K') (hm : m' ≤ m) (hc₀ : c₀ ≤ c₀') :
  C.is_weak_bounded_exact k' K' m' c₀' :=
begin
  intros c hc i hi x ε ε_pos,
  haveI : fact (k ≤ k') := hk,
  obtain ⟨y, hy⟩ := hC c (hc₀.trans hc) i (lt_of_lt_of_le hi hm) (res x) ε ε_pos,
  use y,
  simp only [res_res] at hy,
  refine le_trans hy _,
  rw d_res,
  apply add_le_add_right,
  exact mul_le_mul hK (hC_adm.res_norm_noninc _ _ _ _ (d x)) (norm_nonneg _) ((zero_le K).trans hK)
end

end is_weak_bounded_exact

namespace is_bounded_exact

variables {C C₁ C₂}
variables {k k' K K' : ℝ≥0} {m m' : ℤ} {c₀ c₀' : ℝ≥0} [fact (1 ≤ k)] [fact (1 ≤ k')]

lemma of_le (hC : C.is_bounded_exact k K m c₀)
  (hC_adm : C.admissible) (hk : k ≤ k') (hK : K ≤ K') (hm : m' ≤ m) (hc₀ : c₀ ≤ c₀') :
  C.is_bounded_exact k' K' m' c₀' :=
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

lemma of_iso (h : C₁.is_bounded_exact k K m c₀) (f : C₁ ≅ C₂)
  (hf : ∀ c i, (f.hom.apply : C₁ c i ⟶ C₂ c i).is_strict) :
  C₂.is_bounded_exact k K m c₀ :=
begin
  intros c hc i hi x,
  obtain ⟨y, hy⟩ := h c hc i hi (f.inv.apply x),
  refine ⟨f.hom y, _⟩,
  calc  ∥res x - d (f.hom y)∥
      = ∥res x - f.hom (d y)∥ : by rw d_apply
  ... = ∥f.hom (f.inv (res x)) - f.hom (d y)∥ : by rw hom_apply_inv_apply
  ... = ∥f.hom (f.inv (res x) - d y)∥ : by congr ; exact (f.hom.apply.map_sub _ _).symm
  ... = ∥f.inv (res x) - d y∥ : hf _ _ _
  ... = ∥res (f.inv x) - d y∥ : by rw res_apply
  ... ≤ K * ∥d (f.inv x)∥ : hy
  ... = K * ∥d x∥ : congr_arg _ _,
  calc  ∥d (f.inv x)∥
      = ∥f.inv (d x)∥ : by rw d_apply
  ... = ∥f.hom (f.inv (d x))∥ : (hf _ _ _).symm
  ... = ∥d x∥ : by rw hom_apply_inv_apply
end

lemma of_shift  {k K : ℝ≥0} {m : ℤ} [hk : fact (1 ≤ k)] {c₀ : ℝ≥0}
  (H : ∀ c ≥ c₀, ∀ i < m - 1, ∀ x : C (k * c) (i + 1 + 1),
   ∃ y : C c (i + 1), ∥res x - d y∥ ≤ K * ∥d x∥) :
   C.is_bounded_exact k K m c₀ :=
begin
  intros c hc i hi x,
  specialize H c hc (i-1) (by linarith),
  rw [sub_add_cancel] at H,
  exact H x,
end

end is_bounded_exact

namespace is_weak_bounded_exact

variables {C C₁ C₂}
variables {k k' K K' : ℝ≥0} {m m' : ℤ} {c₀ c₀' : ℝ≥0} [fact (1 ≤ k)] [fact (1 ≤ k')]

lemma to_exact (hC : C.is_weak_bounded_exact k K m c₀) {δ : ℝ≥0} (hδ : 0 < δ)
  (H : ∀ c ≥ c₀, ∀ i < m - 1, ∀ x : C (k * c) (i + 1 + 1),
    d x = 0 → ∃ y : C c (i + 1), res x = d y) : C.is_bounded_exact k (K + δ) m c₀ :=
begin
  apply is_bounded_exact.of_shift,
  intros c hc i hi x,
  by_cases hdx : d x = 0,
  { rcases H c hc i hi x hdx with ⟨y, hy⟩,
    exact ⟨y, by simp [hy, hdx]⟩ },
  { have : ((K + δ : ℝ≥0) : ℝ) * ∥d x∥ = K * ∥d x∥ + δ * ∥d x∥, apply_mod_cast add_mul,
    simp_rw this,
    apply hC c hc _ _ x (δ*∥d x∥) (mul_pos (by exact_mod_cast hδ) $ norm_pos_iff.mpr hdx), linarith },
end

end is_weak_bounded_exact
section quotient

open normed_group_hom

variables {M M'}

/-- The quotient of a system of complexes. -/
def is_quotient (f : M ⟶ M') : Prop :=
∀ c i, normed_group_hom.is_quotient (f.apply : M c i ⟶ M' c i)

-- The next three lemmas restate lemmas about normed_group_hom.is_quotient in terms of the coercion
-- of `M ⟶ M'` to functions.

lemma is_quotient.surjective {f : M ⟶ M'} (h : is_quotient f) {c i} (m' : M' c i) :
  ∃ m : M c i, f m = m' := (h c i).surjective m'

lemma is_quotient.norm_lift {f : M ⟶ M'} (h : is_quotient f) {ε : ℝ} (hε : 0 < ε) {c i}
  (n : M' c i) : ∃ (m : M c i), f m = n ∧ ∥m∥ < ∥n∥ + ε :=
quotient_norm_lift (h c i) hε n

lemma is_quotient.norm_le {f : M ⟶ M'} (h : is_quotient f) {c i} (m : M c i) : ∥f m∥ ≤ ∥m∥ :=
quotient_norm_le (h c i) _

/-- The quotient of an admissible system of complexes is admissible. -/
lemma admissible_of_quotient {f : M ⟶ M'} (hquot : is_quotient f) (hadm : M.admissible) :
  M'.admissible :=
begin
  split,
  { intros c i m',
    refine le_of_forall_pos_le_add _,
    intros ε hε,
    obtain ⟨m, hm : f m = m' ∧ ∥m∥ < ∥m'∥ + ε⟩ := hquot.norm_lift hε m',
    rw [← hm.1, d_apply],
    calc ∥f (d m)∥ ≤ ∥d m∥ : hquot.norm_le _
      ... ≤ ∥m∥ : hadm.d_norm_noninc _ _ m
      ... ≤ ∥m'∥ + ε : le_of_lt hm.2
      ... = ∥f m∥ + ε : by rw [hm.1] },
  { intros c' c i hc m',
    letI h := hc,
    refine le_of_forall_pos_le_add _,
    intros ε hε,
    obtain ⟨m, hm⟩ := hquot.norm_lift hε m',
    rw [← hm.1, res_apply],
    calc ∥f (res m)∥ ≤ ∥res m∥ : hquot.norm_le _
      ... ≤ ∥m∥ : hadm.res_norm_noninc c' c _ hc m
      ... ≤ ∥m'∥ + ε : le_of_lt hm.2
      ... = ∥f m∥ + ε : by rw [hm.1] }
end

end quotient

end system_of_complexes

-- #lint- only unused_arguments def_lemma doc_blame
