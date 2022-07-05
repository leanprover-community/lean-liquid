import for_mathlib.derived.example
import breen_deligne.eval

noncomputable theory

open category_theory category_theory.preadditive

namespace breen_deligne
namespace package

variables (BD : package)
variables {𝒜 : Type*} [category 𝒜] [abelian 𝒜]
variables (F : 𝒜 ⥤ 𝒜)

def eval' : 𝒜 ⥤ cochain_complex 𝒜 ℤ :=
(data.eval_functor F).obj BD.data ⋙ homological_complex.embed complex_shape.embedding.nat_down_int_up

def eval : 𝒜 ⥤ bounded_homotopy_category 𝒜 :=
(data.eval_functor F).obj BD.data ⋙ chain_complex.to_bounded_homotopy_category

instance eval_additive : (BD.eval F).additive :=
functor.additive_of_map_fst_add_snd _ $ λ A,
begin
  refine homotopy_category.eq_of_homotopy _ _ _,
  rw [← functor.map_add],
  exact homological_complex.embed_homotopy _ _ (eval_functor_homotopy F BD A) _,
end

lemma eval_functor_obj_X (X : 𝒜) (n : ℕ) :
  (((data.eval_functor F).obj BD.data).obj X).X n = F.obj ((Pow (BD.data.X n)).obj X) := rfl

lemma eval_functor_obj_d (X : 𝒜) (m n : ℕ) :
  (((data.eval_functor F).obj BD.data).obj X).d m n =
    (universal_map.eval_Pow F (BD.data.d m n)).app X := rfl

lemma eval'_obj_X (X : 𝒜) (n : ℕ) :
  ((BD.eval' F).obj X).X (-n:ℤ) = F.obj ((Pow (BD.data.X n)).obj X) :=
by { cases n; apply eval_functor_obj_X }

lemma eval'_obj_X_0 (X : 𝒜) :
  ((BD.eval' F).obj X).X 0 = F.obj ((Pow (BD.data.X 0)).obj X) := rfl

lemma eval'_obj_X_succ (X : 𝒜) (n : ℕ) :
  ((BD.eval' F).obj X).X -[1+ n] = F.obj ((Pow (BD.data.X (n+1))).obj X) := rfl

lemma eval'_obj_d (X : 𝒜) (m n : ℕ) :
  ((BD.eval' F).obj X).d (-(m+1:ℕ):ℤ) (-(n+1:ℕ):ℤ) =
    (universal_map.eval_Pow F (BD.data.d (m+1) (n+1))).app X := rfl

lemma eval'_obj_d_0 (X : 𝒜) (n : ℕ) :
  ((BD.eval' F).obj X).d (-(n+1:ℕ):ℤ) (-(1:ℕ)+1:ℤ) =
    (universal_map.eval_Pow F (BD.data.d (n+1) 0)).app X := rfl

end package
end breen_deligne
