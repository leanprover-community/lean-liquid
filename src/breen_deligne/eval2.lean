import for_mathlib.derived.example
import breen_deligne.eval

noncomputable theory

open category_theory

namespace breen_deligne
namespace package

variables (BD : package)
variables {𝒜 : Type*} [category 𝒜] [abelian 𝒜]
variables (F : 𝒜 ⥤ 𝒜)

def eval : 𝒜 ⥤ bounded_homotopy_category 𝒜 :=
(data.eval_functor F).obj BD.data ⋙ chain_complex.to_bounded_homotopy_category

instance eval_additive : (BD.eval F).additive :=
functor.additive_of_map_fst_add_snd _ $ λ A,
begin
  refine homotopy_category.eq_of_homotopy _ _ _,
  rw [← functor.map_add],
  exact homological_complex.embed_homotopy _ _ (eval_functor_homotopy F BD A) _,
end

end package
end breen_deligne
