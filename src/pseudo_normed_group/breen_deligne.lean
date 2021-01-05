import pseudo_normed_group.basic
import breen_deligne

noncomputable theory

local attribute [instance] type_pow

open_locale nnreal big_operators matrix

namespace breen_deligne

namespace basic_universal_map

variables {m n : ℕ} (f : basic_universal_map m n)
variables (M : Type*) [pseudo_normed_group M]

open pseudo_normed_group_hom

def eval_png : pseudo_normed_group_hom (M^m) (M^n) :=
mk_to_pi $ λ j, mk_from_pi $ λ i, gsmul $ f j i

lemma eval_png_bound :
  (f.eval_png M).bound = (finset.univ.sup $ λ i, ∑ j, (f i j).nat_abs) :=
by simp only [eval_png, bound_mk_from_pi, mk_to_pi_bound, int.nat_abs, bound_gsmul]

lemma eval_png_apply (x : M^m) : f.eval_png M x = λ j, ∑ i, f j i • (x i) :=
begin
  ext j,
  simp only [eval_png, coe_mk_from_pi, apply_to_fun, add_monoid_hom.apply_apply,
    add_monoid_hom.to_fun_eq_coe, fintype.sum_apply, function.comp_app, coe_gsmul, mk_to_pi_to_fun]
end

@[simp] lemma eval_png_zero : (0 : basic_universal_map m n).eval_png M = 0 :=
begin
  ext,
  { simp only [eval_png_apply, zero_smul, finset.sum_const_zero, matrix.zero_apply], refl },
  { simp only [eval_png_bound, bound_zero, nnreal.coe_zero, nat.cast_zero, nnreal.coe_eq_zero,
      finset.sum_const_zero, matrix.zero_apply, int.nat_abs_zero],
    apply le_antisymm _ (zero_le _),
    apply finset.sup_le, intros, refl }
end

lemma eval_png_comp {l m n} (g : basic_universal_map m n) (f : basic_universal_map l m) :
  (g.comp f).eval_png M = (g.eval_png M).comp (f.eval_png M) :=
begin
  ext,
  { simp only [eval_png_apply, comp_to_fun, add_monoid_hom.coe_comp, add_monoid_hom.to_fun_eq_coe,
      function.comp_app, coe_to_add_monoid_hom, comp, matrix.mul_apply,
      finset.smul_sum, finset.sum_smul, mul_smul],
    rw finset.sum_comm },
  { simp only [eval_png, bound_mk_from_pi, bound_comp, mk_to_pi_bound, int.nat_abs,
      bound_gsmul, nnreal.coe_mul], }
end

end basic_universal_map


end breen_deligne
