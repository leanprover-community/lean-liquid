import breen_deligne.homotopy
import category_theory.preadditive
import category_theory.limits.shapes.finite_products

noncomputable theory

open category_theory category_theory.limits

namespace category_theory
namespace preadditive

variables {𝒜 : Type*} [category 𝒜] [has_zero_morphisms 𝒜] [has_finite_biproducts 𝒜]

-- move this
@[simps {fully_applied := ff}]
def Pow (n : ℕ) : 𝒜 ⥤ 𝒜 :=
{ obj := λ A, ⨁ (λ (i : ulift $ fin n), A),
  map := λ A B f, biproduct.map (λ i, f),
  map_id' := λ A, by { ext i j, simp only [biproduct.ι_map, category.id_comp, category.comp_id], },
  map_comp' := λ A B C f g, by { ext i j, simp only [biproduct.ι_map_assoc, category.assoc], } }

end preadditive
end category_theory

namespace breen_deligne

open category_theory.preadditive

variables (BD : data)
variables {𝒜 : Type*} [category 𝒜] [preadditive 𝒜] [has_finite_biproducts 𝒜]
variables (F : 𝒜 ⥤ 𝒜)

namespace basic_universal_map

variables {m n : ℕ} (f : basic_universal_map m n)

@[simps {fully_applied := ff}]
def eval_Pow : (Pow m : 𝒜 ⥤ 𝒜) ⟶ Pow n :=
{ app := λ A, biproduct.desc $ λ i, biproduct.lift $ λ j, f j.down i.down • 𝟙 A,
  naturality' := begin
    intros, ext i j,
    simp only [Pow_map, biproduct.ι_map_assoc, biproduct.ι_desc_assoc, biproduct.lift_π,
      category.assoc, biproduct.lift_map,
      comp_zsmul, zsmul_comp, category.comp_id, category.id_comp],
  end }

end basic_universal_map

namespace universal_map

variables {m n o : ℕ} (f : universal_map m n) (g : universal_map n o)

-- @[simps {fully_applied := ff}]
def eval_Pow : Pow m ⋙ F ⟶ Pow n ⋙ F :=
{ app := λ A, free_abelian_group.lift (λ g, F.map ((basic_universal_map.eval_Pow g).app A)) f,
  naturality' := begin
    intros A B φ,
    dsimp,
    -- need to rewrite `free_abelian_group.lift` as a `finset.sum`.
    sorry
  end }

lemma eval_Pow_zero_app (A : 𝒜) : (eval_Pow F (0 : universal_map m n)).app A = 0 :=
add_monoid_hom.map_zero _

@[simp] lemma eval_Pow_zero : eval_Pow F (0 : universal_map m n) = 0 :=
by { ext A, rw eval_Pow_zero_app, refl }

lemma eval_Pow_comp_app (A : 𝒜) :
  (eval_Pow F (universal_map.comp g f)).app A = (eval_Pow F f).app A ≫ (eval_Pow F g).app A :=
sorry

lemma eval_Pow_comp : eval_Pow F (universal_map.comp g f) = eval_Pow F f ≫ eval_Pow F g :=
by { ext A, rw eval_Pow_comp_app, refl }

end universal_map

namespace data

def eval_functor.obj (M : 𝒜) : chain_complex 𝒜 ℕ :=
{ X := λ n, (Pow (BD.X n) ⋙ F).obj M,
  d := λ m n, ((BD.d m n).eval_Pow F).app M,
  shape' := λ i j h, by rw [BD.shape i j h, universal_map.eval_Pow_zero_app],
  d_comp_d' := λ i j k hij hjk, begin
    rw [← universal_map.eval_Pow_comp_app],
    have := BD.d_comp_d i j k,
    convert universal_map.eval_Pow_zero_app _ _ using 3,
  end }

def eval_functor : 𝒜 ⥤ chain_complex 𝒜 ℕ :=
{ obj := eval_functor.obj BD F,
  map := λ A B f,
  { f := λ n, (Pow (BD.X n) ⋙ F).map f,
    comm' := λ m n h, sorry },
  map_id' := λ A, by { ext n, exact category_theory.functor.map_id _ _ },
  map_comp' := λ A B C f g, by { ext n, exact category_theory.functor.map_comp _ _ _ } }

end data

end breen_deligne
