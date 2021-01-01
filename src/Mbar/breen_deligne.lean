import Mbar.Mbar_le
import breen_deligne
import normed_group_hom

local attribute [instance] type_pow

noncomputable theory

open_locale big_operators

-- move this
instance normed_group_pow (V : Type*) (n : ℕ) [normed_group V] :
  normed_group (V^n) :=
pi.normed_group

namespace breen_deligne

namespace basic_universal_map

variables {k m n : ℕ}
variables (r' : ℝ) (S : Type*) [fintype S] [fact (0 < r')]
variables (f : basic_universal_map m n)

def eval_Mbar : normed_group_hom ((Mbar r' S)^m) ((Mbar r' S)^n) :=
normed_group_hom.mk_to_pi _ $
λ i, normed_group_hom.mk_from_pi _ _ $
λ j, normed_group.gsmul (f i j)

@[simp] lemma eval_Mbar_zero : (eval_Mbar r' S (0 : basic_universal_map m n)) = 0 :=
begin
  ext F i s k,
  simp only [eval_Mbar, pi.zero_apply, normed_group_hom.coe_zero, zero_gsmul,
    normed_group_hom.mk_from_pi_to_fun, finset.sum_const_zero, normed_group.gsmul_to_fun,
    normed_group_hom.mk_to_pi_to_fun],
end

@[simp] lemma eval_Mbar_comp (g : basic_universal_map m n) (f : basic_universal_map k m) :
  (g.comp f).eval_Mbar r' S = (g.eval_Mbar r' S).comp (f.eval_Mbar r' S) :=
begin
  ext F i s ℓ,
  simp only [eval_Mbar, normed_group_hom.mk_from_pi_to_fun, add_monoid_hom.coe_comp,
    normed_group_hom.comp_to_fun, add_monoid_hom.to_fun_eq_coe, function.comp_app,
    normed_group.gsmul_to_fun, normed_group_hom.mk_to_pi_to_fun,
    normed_group_hom.mk_to_pi, normed_group_hom.mk_from_pi],
  dsimp,
  sorry
end

end basic_universal_map

namespace universal_map

variables {m n : ℕ}
variables (r' : ℝ) (S : Type*) [fintype S] [fact (0 < r')]

def eval_Mbar : universal_map m n →+ normed_group_hom ((Mbar r' S)^m) ((Mbar r' S)^n) :=
free_abelian_group.lift $ basic_universal_map.eval_Mbar _ _

end universal_map

end breen_deligne
