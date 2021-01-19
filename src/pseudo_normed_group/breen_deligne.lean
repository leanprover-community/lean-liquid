import pseudo_normed_group.basic
import breen_deligne

noncomputable theory

local attribute [instance] type_pow

open_locale nnreal big_operators matrix

namespace breen_deligne

namespace basic_universal_map

variables {m n : ℕ} (f : basic_universal_map m n)
variables (M : Type*) [pseudo_normed_group M]

open add_monoid_hom pseudo_normed_group

def eval_png : (M^m) →+ (M^n) :=
mk_to_pi $ λ j, mk_from_pi $ λ i, const_smul_hom _ $ f j i

lemma eval_png_apply (x : M^m) : f.eval_png M x = λ j, ∑ i, f j i • (x i) :=
begin
  ext j,
  simp only [eval_png, coe_mk_from_pi, add_monoid_hom.apply_apply, mk_to_pi_apply,
    add_monoid_hom.to_fun_eq_coe, fintype.sum_apply, function.comp_app, coe_gsmul,
    @mk_from_pi_apply M _ (fin m) _ (λ _, M) _ _ x, const_smul_hom_apply]
end

@[simp] lemma eval_png_zero : (0 : basic_universal_map m n).eval_png M = 0 :=
by { ext, simp only [eval_png_apply, zero_smul, finset.sum_const_zero, matrix.zero_apply], refl }

lemma eval_png_mem_filtration :
  (f.eval_png M) ∈ filtration ((M^m) →+ (M^n)) (finset.univ.sup $ λ i, ∑ j, (f i j).nat_abs) :=
begin
  apply mk_to_pi_mem_filtration,
  intro j,
  refine filtration_mono (finset.le_sup (finset.mem_univ j)) (mk_from_pi_mem_filtration _ _),
  intros i,
  exact const_smul_hom_int_mem_filtration _ _ le_rfl
end

lemma eval_png_comp {l m n} (g : basic_universal_map m n) (f : basic_universal_map l m) :
  (g.comp f).eval_png M = (g.eval_png M).comp (f.eval_png M) :=
begin
  ext x j,
  simp only [eval_png_apply, function.comp_app, coe_comp, basic_universal_map.comp,
    matrix.mul_apply, finset.smul_sum, finset.sum_smul, mul_smul],
  rw finset.sum_comm
end

end basic_universal_map

end breen_deligne
#lint- only unused_arguments
