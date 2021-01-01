import Mbar.Mbar_le
import breen_deligne
import normed_group_hom

local attribute [instance] type_pow

noncomputable theory

-- move this
instance normed_group_pow (V : Type*) (n : ℕ) [normed_group V] :
  normed_group (V^n) :=
pi.normed_group

namespace breen_deligne

namespace basic_universal_map

variables {m n : ℕ}
variables (r' : ℝ) (S : Type*) [fintype S] [fact (0 < r')]
variables (f : basic_universal_map m n)

def eval_Mbar : normed_group_hom ((Mbar r' S)^m) ((Mbar r' S)^n) :=
normed_group_hom.mk_to_pi _ $
λ i, normed_group_hom.mk_from_pi _ _ $
λ j, normed_group.gsmul (f i j)

end basic_universal_map

namespace universal_map

variables {m n : ℕ}
variables (r' : ℝ) (S : Type*) [fintype S] [fact (0 < r')]

def eval_Mbar : universal_map m n →+ normed_group_hom ((Mbar r' S)^m) ((Mbar r' S)^n) :=
free_abelian_group.lift $ basic_universal_map.eval_Mbar _ _

end universal_map

end breen_deligne
