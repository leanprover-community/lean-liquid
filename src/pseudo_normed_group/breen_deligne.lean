import pseudo_normed_group.basic
import pseudo_normed_group.category
import breen_deligne.suitable

/-!

# Universal maps and pseudo-normed groups

This file contains the definition of the action of a basic universal map
on powers of a pseudo-normed group and related types.

## Main definitions

- `f.eval_png : (M^m) →+ (M^n)` : the group homomorphism induced by a basic universal map.
- `f.eval_png₀ : M_{c₁}^m → M_{c₂}^n` : the induced map if `f` is (c₁, c₂)-suitable.

-/
noncomputable theory

local attribute [instance] type_pow

open_locale nnreal big_operators matrix

namespace breen_deligne

namespace basic_universal_map

variables {m n : ℕ} (f : basic_universal_map m n)
variables (M : Type*)

section pseudo_normed_group

variables [pseudo_normed_group M]

open add_monoid_hom pseudo_normed_group

end pseudo_normed_group

section profinitely_filtered_pseudo_normed_group

open pseudo_normed_group profinitely_filtered_pseudo_normed_group add_monoid_hom

open comphaus_filtered_pseudo_normed_group_hom comphaus_filtered_pseudo_normed_group

variables [profinitely_filtered_pseudo_normed_group M]

/-- `eval_png M f` is the homomorphism `M^m → M^n` of profinitely filtered pseudo-normed groups
obtained by matrix multiplication with the matrix `f`. -/
def eval_png : basic_universal_map m n →+
  comphaus_filtered_pseudo_normed_group_hom (M ^ m) (M ^ n) :=
add_monoid_hom.mk' (λ f, pi_lift (λ j, ∑ i, f j i • pi_proj i)
  begin
    let C : ℝ≥0 := finset.univ.sup (λ j, ∑ i, (f j i).nat_abs),
    refine ⟨C, λ j, _⟩,
    intros c x hx,
    have : ∑ i, (↑(f j i).nat_abs * (1 * c)) ≤ C * c,
    { rw ← finset.sum_mul, exact mul_le_mul' (finset.le_sup (finset.mem_univ j)) (one_mul c).le },
    refine filtration_mono this _,
    simp only [← coe_to_add_monoid_hom, ← to_add_monoid_hom_hom_apply,
      add_monoid_hom.map_sum, add_monoid_hom.map_zsmul, add_monoid_hom.finset_sum_apply],
    refine sum_mem_filtration _ _ _ _,
    rintro i -,
    refine int_smul_mem_filtration _ _ _ _,
    exact @pi_proj_bound_by _ (λ _, M) _ i _ _ hx,
  end)
  begin
    intros f g,
    ext x j,
    simp only [← coe_to_add_monoid_hom, ← to_add_monoid_hom_hom_apply,
      add_monoid_hom.map_add, add_monoid_hom.add_apply, pi.add_apply],
    simp only [coe_to_add_monoid_hom, to_add_monoid_hom_hom_apply],
    simp only [pi_lift_to_fun, mk_to_pi_apply, ← to_add_monoid_hom_hom_apply,
      add_monoid_hom.map_sum, add_monoid_hom.map_zsmul, add_monoid_hom.finset_sum_apply],
    rw ← finset.sum_add_distrib,
    simp only [pi_proj_to_fun, to_add_monoid_hom_hom_apply, coe_smul,
      coe_to_add_monoid_hom, pi.smul_apply, add_smul],
    refl
  end

lemma eval_png_apply (x : M^m) : eval_png M f x = λ j, ∑ i, f j i • (x i) :=
begin
  ext j,
  simp only [eval_png, mk'_apply, pi_lift_to_fun, mk_to_pi_apply, ← to_add_monoid_hom_hom_apply],
  simp only [add_monoid_hom.map_sum, add_monoid_hom.map_zsmul,
    add_monoid_hom.finset_sum_apply],
  refl
end

lemma eval_png_mem_filtration :
  (eval_png M f).to_add_monoid_hom ∈
    filtration ((M^m) →+ (M^n)) (finset.univ.sup $ λ i, ∑ j, (f i j).nat_abs) :=
begin
  apply mk_to_pi_mem_filtration,
  intro j,
  let C : ℝ≥0 := finset.univ.sup (λ j, ∑ i, (f j i).nat_abs),
  intros c x hx,
  have : ∑ i, (↑(f j i).nat_abs * (1 * c)) ≤ C * c,
  { rw ← finset.sum_mul, exact mul_le_mul' (finset.le_sup (finset.mem_univ j)) (one_mul c).le },
  refine filtration_mono this _,
  simp only [← coe_to_add_monoid_hom, ← to_add_monoid_hom_hom_apply,
    add_monoid_hom.map_sum, add_monoid_hom.map_zsmul, add_monoid_hom.finset_sum_apply],
  refine sum_mem_filtration _ _ _ _,
  rintro i -,
  refine int_smul_mem_filtration _ _ _ _,
  exact @pi_proj_bound_by _ (λ _, M) _ i _ _ hx,
end

lemma eval_png_mem_filtration' (c₁ c₂ : ℝ≥0) [h : f.suitable c₁ c₂]
  (x : M^m) (hx : x ∈ filtration (M^m) c₁) :
  (eval_png M f x) ∈ filtration (M^n) c₂ :=
filtration_mono (f.sup_mul_le c₁ c₂) (f.eval_png_mem_filtration M hx)

/-- `f.eval_png₀ M` is the group homomorphism `(M^m) →+ (M^n)`
obtained by matrix multiplication with the matrix `f`,
but restricted to `(filtration M c₁)^m → (filtration M c₂)^n`. -/
@[simps {fully_applied := ff}]
def eval_png₀ (c₁ c₂ : ℝ≥0) [h : f.suitable c₁ c₂] (x : filtration (M^m) c₁) :
  filtration (M^n) c₂ :=
⟨eval_png M f x, eval_png_mem_filtration' f M c₁ c₂ x x.2⟩

lemma eval_png_comp {l m n} (g : basic_universal_map m n) (f : basic_universal_map l m) :
  eval_png M (basic_universal_map.comp g f) = (eval_png M g).comp (eval_png M f) :=
begin
  ext x j,
  simp only [eval_png_apply, function.comp_app, coe_comp, basic_universal_map.comp, comp_to_fun,
    matrix.mul_apply, finset.smul_sum, finset.sum_smul, mul_smul, add_monoid_hom.mk'_apply],
  rw finset.sum_comm
end

lemma eval_png₀_continuous (c₁ c₂ : ℝ≥0) [f.suitable c₁ c₂] : continuous (f.eval_png₀ M c₁ c₂) :=
(eval_png M f).continuous _ (λ x, rfl)

end profinitely_filtered_pseudo_normed_group

end basic_universal_map

end breen_deligne

#lint- only unused_arguments def_lemma doc_blame
