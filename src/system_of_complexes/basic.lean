import algebra.ordered_group
import category_theory.preadditive.functor_category

import for_mathlib.normed_group_quotient

import normed_group.NormedGroup
import locally_constant.Vhat -- NormedGroup is preadditive (maybe rename this file, or split it)
import system_of_complexes.complex

import facts

import tactic.gptf

universe variables v u
noncomputable theory
open opposite category_theory
open_locale nnreal

/-!

# Systems of complexes of normed abelian groups

In this file we define systems of complexes of normed abelian groups,
as in of Definition 9.3 of [Analytic].

## Main declarations

* `system_of_complexes`: a system of complexes of normed abelian groups. See Definition 4.1
  of the blueprint.
* `admissible`: such a system is *admissible* if all maps that occur in the system
    are norm-nonincreasing. See Definition 4.2 of the blueprint.
* `is_bounded_exact`: an exactness criterion for such systems, See Definition 4.3 of the
  blueprint. It asks for a suitable interplay between the norms and the algebraic properties
  of the system.
* `is_weak_bounded_exact` : another exactness criterion for such systems. See Definition 4.4
   of the blueprint.

## TODO

It seems a bit ridiculous that this file has to import `locally_constant.Vhat`.

-/

-- TODO: at some point we can abstract the following definition over `NormedGroup` and `ℝ≥0`.
-- But I don't think that is relevant for this project.

/-- A system of complexes of normed abelian groups, indexed by `ℝ≥0`.
See also Definition 9.3 of [Analytic]. -/
@[derive category_theory.category]
def system_of_complexes : Type* := ℝ≥0ᵒᵖ ⥤ (cochain_complex ℕ NormedGroup)

-- instance : has_shift system_of_complexes := has_shift.mk $ (shift _).congr_right

variables {M M' N : system_of_complexes.{u}} (f : M ⟶ M') (g : M' ⟶ N)

instance : has_coe_to_fun system_of_complexes :=
⟨λ C, ℝ≥0 → ℕ → NormedGroup, λ C c i, (C.obj $ op c).X i⟩

/-- `f.apply c i` is application of the natural transformation `f`: $f_c^i : M_c^i ⟶ N_c^i$. -/
def quiver.hom.apply (f : M ⟶ N) {c : ℝ≥0} {i : ℕ} : M c i ⟶ N c i :=
(f.app (op c)).f i

instance hom_to_fun : has_coe_to_fun (M ⟶ N) :=
⟨λ f, Π {c : ℝ≥0} {i : ℕ}, M c i → N c i, λ f {c} {i} x, f.apply x⟩

instance : preadditive system_of_complexes := functor.preadditive

lemma system_of_complexes.map_sub (f : M ⟶ N) {c i} (m m' : M c i) : f (m-m') = f m - f m' :=
normed_group_hom.map_sub _ _ _

/-- `f.apply c i` is application of the natural isomorphism `f`: $f_c^i : M_c^i ≅ N_c^i$. -/
def category_theory.iso.apply (f : M ≅ N) {c : ℝ≥0} {i : ℕ} : M c i ≅ N c i :=
differential_object.complex_like.iso_app (f.app (op c)) i

namespace system_of_complexes

variables (C C₁ C₂ : system_of_complexes.{u})

/-- `res` is the restriction map `C c' i ⟶ C c i` for a system of complexes `C`,
and nonnegative reals `c ≤ c'`. -/
def res {C : system_of_complexes} {c' c : ℝ≥0} {i : ℕ} [h : fact (c ≤ c')] : C c' i ⟶ C c i :=
(C.map (hom_of_le h.out).op).f i

variables {c₁ c₂ c₃ : ℝ≥0} (i j : ℕ)

@[simp] lemma res_comp_res (h₁ : fact (c₂ ≤ c₁)) (h₂ : fact (c₃ ≤ c₂)) :
  @res C _ _ i h₁ ≫ @res C _ _ i h₂ = @res C _ _ i ⟨h₂.out.trans h₁.out⟩ :=
begin
  have := (category_theory.functor.map_comp C (hom_of_le h₁.out).op (hom_of_le h₂.out).op),
  rw [← op_comp] at this,
  delta res,
  erw this,
  refl,
end

@[simp] lemma res_res (h₁ : fact (c₂ ≤ c₁)) (h₂ : fact (c₃ ≤ c₂)) (x : C c₁ i) :
  @res C _ _ i h₂ (@res C _ _ i h₁ x) = @res C _ _ i ⟨h₂.out.trans h₁.out⟩ x :=
by { rw ← (C.res_comp_res i h₁ h₂), refl }

/-- `C.d` is the differential `C c i ⟶ C c (i+1)` for a system of complexes `C`. -/
def d (C : system_of_complexes) {c : ℝ≥0} (i j : ℕ) : C c i ⟶ C c j :=
(C.obj $ op c).d i j

lemma d_eq_zero (c : ℝ≥0) (h : i + 1 ≠ j) : (C.d i j : C c i ⟶ C c j) = 0 :=
(C.obj $ op c).d_eq_zero h

lemma d_eq_zero_apply (c : ℝ≥0) (h : i + 1 ≠ j) (x : C c i) : (C.d i j x) = 0 :=
by { rw [d_eq_zero C i j c h], refl }

@[simp] lemma d_self_apply (c : ℝ≥0) (x : C c i) : (C.d i i x) = 0 :=
d_eq_zero_apply _ _ _ _ i.succ_ne_self _

lemma d_comp_d (c : ℝ≥0) (i j k : ℕ) : C.d i j ≫ (C.d j k : C c j ⟶ _) = 0 :=
(C.obj $ op c).d_comp_d _ _ _

@[simp] lemma d_d (c : ℝ≥0) (i j k : ℕ) (x : C c i) :
  C.d j k (C.d i j x) = 0 :=
show ((C.d i j) ≫ C.d j k) x = 0, by { rw d_comp_d, refl }

lemma d_comp_res (h : fact (c₂ ≤ c₁)) :
  C.d i j ≫ @res C _ _ _ h = @res C _ _ _ _ ≫ C.d i j :=
(C.map (hom_of_le h.out).op).comm _ _

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
def congr {c c' : ℝ≥0} {i i' : ℕ} (hc : c = c') (hi : i = i') :
  C c i ⟶ C c' i' :=
eq_to_hom $ by { subst hc, subst hi }

variables (M M' N)

lemma d_apply (f : M ⟶ N) {c : ℝ≥0} {i j : ℕ} (m : M c i) :
  N.d i j (f m) = f (M.d i j m) :=
begin
  show (_ ≫ N.d i j) m = (M.d i j ≫ _) m,
  congr' 1,
  exact ((f.app (op c)).comm i j).symm
end

lemma res_comp_apply (f : M ⟶ N) (c c' : ℝ≥0) [h : fact (c ≤ c')] (i : ℕ) :
  @res M c' c i _ ≫ f.apply = f.apply ≫ res :=
congr_fun (congr_arg differential_object.hom.f (f.naturality (hom_of_le h.out).op)) i

lemma res_apply (f : M ⟶ N) (c c' : ℝ≥0) [h : fact (c ≤ c')] {i : ℕ} (m : M c' i) :
  @res N c' c _ _ (f m) = f (res m) :=
show (f.apply ≫ (@res N c' c _ _)) m = (@res M c' c _ _ ≫ (f.apply)) m,
by rw res_comp_apply

/-- A system of complexes is *admissible*
if all the differentials and restriction maps are norm-nonincreasing.

See Definition 9.3 of [Analytic]. -/
structure admissible (C : system_of_complexes) : Prop :=
(d_norm_noninc' : ∀ c i j (h : i + 1 = j), (C.d i j : C c i ⟶ C c j).norm_noninc)
(res_norm_noninc : ∀ c' c i h, (@res C c' c i h).norm_noninc)

lemma admissible.d_norm_noninc (hC : C.admissible) (c : ℝ≥0) (i j : ℕ) :
  (C.d i j : C c i ⟶ _).norm_noninc :=
begin
  by_cases h : i + 1 = j,
  { exact hC.d_norm_noninc' c i j h },
  { rw C.d_eq_zero i j c h, intro v, simp }
end

/-- `is_bounded_exact k K m c₀` is a predicate on systems of complexes.

A system of complexes `C` is `(k,K)`-exact in degrees `≤ m` for `c ≥ c₀`*
if the following condition is satisfied:
For all `c ≥ c₀` and all `x : C (k * c) i` with `i ≤ m` there is some `y : C c (i-1)`
(which is defined to be `0` when `i = 0`) such that `∥(C.res x) - (C.d y)∥ ≤ K * ∥C.d x∥`.

See Definition 9.3 of [Analytic] (which coalesces the roles of `k` and `K`).

Implementation details:
* Because we have a differential `d i j : C c i ⟶ C c j` for all `i` and `j`,
  and because `d 0 0 = 0` and `0 - 1 = 0` in Lean's natural numbers,
  we automatically take care of the parenthetical condition about `i = 0`.
* We phrase the condition in a somewhat roundabout way, as
  ```
  ∃ (i₀ j : ℕ) (hi₀ : i₀ = i - 1) (hj : i + 1 = j)
    (y : C c i₀), ∥res x - C.d _ _ y∥ ≤ K * ∥C.d i j x∥
  ```
  This is a hack around an inconvenience known as dependent type theory hell. -/
def is_bounded_exact
  (k K : ℝ≥0) (m : ℕ) [hk : fact (1 ≤ k)] (c₀ : ℝ≥0) : Prop :=
∀ c (hc : fact (c₀ ≤ c)) i (hi : i ≤ m) (x : C (k * c) i),
∃ (i₀ j : ℕ) (hi₀ : i₀ = i - 1) (hj : i + 1 = j)
  (y : C c i₀), ∥res x - C.d _ _ y∥ ≤ K * ∥C.d i j x∥

/-- Weak version of `is_bounded_exact`. -/
def is_weak_bounded_exact
  (k K : ℝ≥0) (m : ℕ) [hk : fact (1 ≤ k)] (c₀ : ℝ≥0) : Prop :=
∀ c (hc : fact (c₀ ≤ c)) i (hi : i ≤ m) (x : C (k * c) i) (ε : ℝ) (hε : 0 < ε),
∃ (i₀ j : ℕ) (hi₀ : i₀ = i - 1) (hj : i + 1 = j)
  (y : C c i₀), ∥res x - C.d _ _ y∥ ≤ K * ∥C.d i j x∥ + ε

namespace is_weak_bounded_exact

variables {C C₁ C₂}
variables {k k' K K' : ℝ≥0} {m m' : ℕ} {c₀ c₀' : ℝ≥0} [fact (1 ≤ k)] [fact (1 ≤ k')]

lemma of_le (hC : C.is_weak_bounded_exact k K m c₀) (hC_adm : C.admissible)
  (hk : fact (k ≤ k')) (hK : fact (K ≤ K')) (hm : m' ≤ m) (hc₀ : fact (c₀ ≤ c₀')) :
  C.is_weak_bounded_exact k' K' m' c₀' :=
begin
  intros c hc i hi x ε ε_pos,
  haveI : fact (k ≤ k') := hk,
  obtain ⟨i', j, hi', hj, y, hy⟩ := hC c ⟨hc₀.out.trans hc.out⟩ i (hi.trans hm) (res x) ε ε_pos,
  use [i', j, hi', hj, y],
  simp only [res_res] at hy,
  refine le_trans hy _,
  rw d_res,
  apply add_le_add_right,
  exact mul_le_mul hK.out (hC_adm.res_norm_noninc _ _ _ _ (C.d _ _ x))
    (norm_nonneg _) ((zero_le K).trans hK.out)
end

lemma of_iso (h : C₁.is_weak_bounded_exact k K m c₀) (f : C₁ ≅ C₂)
  (hf : ∀ c i, @isometry (C₁ c i) (C₂ c i) _ _ (f.hom.apply : C₁ c i ⟶ C₂ c i)) :
  C₂.is_weak_bounded_exact k K m c₀ :=
begin
  intros c hc i hi x ε hε,
  obtain ⟨i', j, hi', hj, y, hy⟩ := h c hc i hi (f.inv.apply x) ε hε,
  refine ⟨i', j, hi', hj, f.hom y, _⟩,
  calc  ∥res x - C₂.d _ _ (f.hom y)∥
      = ∥res x - f.hom (C₁.d _ _ y)∥ : by rw d_apply
  ... = ∥f.hom (f.inv (res x)) - f.hom (C₁.d _ _ y)∥ : by rw hom_apply_inv_apply
  ... = ∥f.hom (f.inv (res x) - C₁.d _ _ y)∥ : by congr ; exact (f.hom.apply.map_sub _ _).symm
  ... = ∥f.inv (res x) - C₁.d _ _ y∥ : normed_group_hom.norm_eq_of_isometry (hf _ _) _
  ... = ∥res (f.inv x) - C₁.d _ _ y∥ : by rw res_apply
  ... ≤ K * ∥C₁.d _ _ (f.inv x)∥ + ε : hy
  ... = K * ∥C₂.d _ _ x∥ + ε : _,
  congr' 2,
  calc  ∥C₁.d i j (f.inv x)∥
      = ∥f.inv (C₂.d i j x)∥ : by rw d_apply
  ... = ∥f.hom (f.inv (C₂.d _ _ x))∥ : (normed_group_hom.norm_eq_of_isometry (hf _ _) _).symm
  ... = ∥C₂.d _ _ x∥ : by rw hom_apply_inv_apply
end

lemma iff_of_iso (f : C₁ ≅ C₂)
  (hf : ∀ c i, @isometry (C₁ c i) (C₂ c i) _ _ (f.hom.apply : C₁ c i ⟶ C₂ c i)) :
  C₁.is_weak_bounded_exact k K m c₀ ↔ C₂.is_weak_bounded_exact k K m c₀ :=
begin
  refine ⟨λ h, h.of_iso f hf, λ h, h.of_iso f.symm _⟩,
  -- TODO: factor this out into a lemma
  intros c n,
  apply normed_group_hom.isometry_of_norm,
  intro v,
  rw ← normed_group_hom.norm_eq_of_isometry (hf c n),
  simp only [←apply_hom_eq_hom_apply, ←apply_inv_eq_inv_apply, iso.symm_hom, coe_inv_hom_id],
end

end is_weak_bounded_exact

namespace is_bounded_exact

variables {C C₁ C₂}
variables {k k' K K' : ℝ≥0} {m m' : ℕ} {c₀ c₀' : ℝ≥0} [fact (1 ≤ k)] [fact (1 ≤ k')]

lemma of_le (hC : C.is_bounded_exact k K m c₀)
  (hC_adm : C.admissible) (hk : k ≤ k') (hK : K ≤ K') (hm : m' ≤ m) (hc₀ : c₀ ≤ c₀') :
  C.is_bounded_exact k' K' m' c₀' :=
begin
  intros c hc i hi x,
  haveI : fact (k ≤ k') := ⟨hk⟩,
  obtain ⟨i', j, hi', hj, y, hy⟩ := hC c ⟨hc₀.trans hc.out⟩ i (hi.trans hm) (res x),
  use [i', j, hi', hj, y],
  simp only [res_res] at hy,
  refine le_trans hy _,
  rw d_res,
  exact mul_le_mul hK (hC_adm.res_norm_noninc _ _ _ _ (C.d _ _ x)) (norm_nonneg _) ((zero_le K).trans hK)
end

lemma of_iso (h : C₁.is_bounded_exact k K m c₀) (f : C₁ ≅ C₂)
  (hf : ∀ c i, @isometry (C₁ c i) (C₂ c i) _ _ (f.hom.apply : C₁ c i ⟶ C₂ c i)) :
  C₂.is_bounded_exact k K m c₀ :=
begin
  intros c hc i hi x,
  obtain ⟨i', j, hi', hj, y, hy⟩ := h c hc i hi (f.inv.apply x),
  refine ⟨i', j, hi', hj, f.hom y, _⟩,
  calc  ∥res x - C₂.d _ _ (f.hom y)∥
      = ∥res x - f.hom (C₁.d _ _ y)∥ : by rw d_apply
  ... = ∥f.hom (f.inv (res x)) - f.hom (C₁.d _ _ y)∥ : by rw hom_apply_inv_apply
  ... = ∥f.hom (f.inv (res x) - C₁.d _ _ y)∥ : by congr ; exact (f.hom.apply.map_sub _ _).symm
  ... = ∥f.inv (res x) - C₁.d _ _ y∥ : normed_group_hom.norm_eq_of_isometry (hf _ _) _
  ... = ∥res (f.inv x) - C₁.d _ _ y∥ : by rw res_apply
  ... ≤ K * ∥C₁.d _ _ (f.inv x)∥ : hy
  ... = K * ∥C₂.d _ _ x∥ : congr_arg _ _,
  calc  ∥C₁.d i j (f.inv x)∥
      = ∥f.inv (C₂.d i j x)∥ : by rw d_apply
  ... = ∥f.hom (f.inv (C₂.d _ _ x))∥ : (normed_group_hom.norm_eq_of_isometry (hf _ _) _).symm
  ... = ∥C₂.d _ _ x∥ : by rw hom_apply_inv_apply
end

end is_bounded_exact

namespace is_weak_bounded_exact

variables {C C₁ C₂}
variables {k k' K K' : ℝ≥0} {m m' : ℕ} {c₀ c₀' : ℝ≥0} [fact (1 ≤ k)] [fact (1 ≤ k')]

lemma to_exact (hC : C.is_weak_bounded_exact k K m c₀)
  [∀ c i, separated_space (C c i)]
  {δ : ℝ≥0} (hδ : 0 < δ)
  (H : ∀ c ≥ c₀, ∀ i ≤ m, ∀ x : C (k * c) i, ∀ j, i+1 = j →
    C.d _ j x = 0 → ∃ (i₀ : ℕ) (hi₀ : i₀ = i - 1) (y : C c i₀), res x = C.d _ _ y) :
  C.is_bounded_exact k (K + δ) m c₀ :=
begin
  intros c hc i hi x,
  by_cases hdx : C.d _ (i+1) x = 0,
  { rcases H c hc.out i hi x _ rfl hdx with ⟨i₀, hi₀, y, hy⟩,
    exact ⟨i₀, _, hi₀, rfl, y, by simp [hy, hdx]⟩ },
  { obtain ⟨i', j, hi', rfl, y, hy⟩ :=
      hC c hc _ hi x (δ*∥C.d _ (i+1) x∥) (mul_pos (by exact_mod_cast hδ) $ norm_pos_iff'.mpr hdx),
    refine ⟨i', _, hi', rfl, y, _⟩,
    have : ((K + δ : ℝ≥0) : ℝ) * ∥C.d _ (i+1) x∥
      = K * ∥C.d _ (i+1) x∥ + δ * ∥C.d _ (i+1) x∥, apply_mod_cast add_mul,
    rwa this },
end

end is_weak_bounded_exact
section quotient

open normed_group_hom

variables {M M'}

/-- The quotient of a system of complexes. -/
def is_quotient (f : M ⟶ M') : Prop :=
∀ c i, add_subgroup.is_quotient (f.apply : M c i ⟶ M' c i)

-- The next three lemmas restate lemmas about normed_group_hom.is_quotient in terms of the coercion
-- of `M ⟶ M'` to functions.

lemma is_quotient.surjective {f : M ⟶ M'} (h : is_quotient f) {c i} (m' : M' c i) :
  ∃ m : M c i, f m = m' := (h c i).surjective m'

lemma is_quotient.norm_lift {f : M ⟶ M'} (h : is_quotient f) {ε : ℝ} (hε : 0 < ε) {c i}
  (n : M' c i) : ∃ (m : M c i), f m = n ∧ ∥m∥ < ∥n∥ + ε :=
(h c i).norm_lift hε n

lemma is_quotient.norm_le {f : M ⟶ M'} (h : is_quotient f) {c i} (m : M c i) : ∥f m∥ ≤ ∥m∥ :=
(h c i).norm_le _

/-- The quotient of an admissible system of complexes is admissible. -/
lemma admissible_of_quotient {f : M ⟶ M'} (hquot : is_quotient f) (hadm : M.admissible) :
  M'.admissible :=
begin
  split,
  { intros c i j h m',
    refine le_of_forall_pos_le_add _,
    intros ε hε,
    obtain ⟨m, hm : f m = m' ∧ ∥m∥ < ∥m'∥ + ε⟩ := hquot.norm_lift hε m',
    rw [← hm.1, d_apply],
    calc ∥f (M.d _ _ m)∥ ≤ ∥M.d _ _ m∥ : hquot.norm_le _
      ... ≤ ∥m∥ : hadm.d_norm_noninc _ _ _ _ m
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
