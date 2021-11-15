import category_theory.preadditive.functor_category
import category_theory.limits.shapes.finite_products

import for_mathlib.homological_complex2

import breen_deligne.homotopy

noncomputable theory

open_locale big_operators

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

-- move this
attribute [simps] comp_hom

end preadditive
end category_theory

namespace breen_deligne

open category_theory.preadditive

variables (BD : data)
variables {𝒜 : Type*} [category 𝒜] [preadditive 𝒜] [has_finite_biproducts 𝒜]
variables (F : 𝒜 ⥤ 𝒜)

namespace basic_universal_map

variables {m n o : ℕ} (f : basic_universal_map m n) (g : basic_universal_map n o)

@[simps {fully_applied := ff}]
def eval_Pow : (Pow m : 𝒜 ⥤ 𝒜) ⟶ Pow n :=
{ app := λ A, biproduct.matrix (λ i j, f j.down i.down • 𝟙 A),
  naturality' := begin
    intros, ext i j,
    simp only [Pow_map, biproduct.ι_map_assoc, category.assoc, biproduct.matrix_π,
      biproduct.map_π, biproduct.ι_desc, biproduct.matrix_π_assoc, biproduct.ι_desc_assoc,
      comp_zsmul, zsmul_comp, category.comp_id, category.id_comp],
  end }

@[simp] lemma eval_Pow_comp : @eval_Pow 𝒜 _ _ _ _ _ (comp g f) = f.eval_Pow ≫ g.eval_Pow :=
begin
  ext A i j,
  simp only [eval_Pow_app, nat_trans.comp_app, category.assoc, biproduct.ι_map_assoc,
    biproduct.matrix_π, biproduct.ι_matrix_assoc, biproduct.lift_desc,
    biproduct.map_π, biproduct.ι_desc, biproduct.matrix_π_assoc, biproduct.ι_desc_assoc,
    comp_zsmul, zsmul_comp, category.comp_id, category.id_comp],
  simp only [comp, add_monoid_hom.mk'_apply, matrix.mul, matrix.dot_product,
    finset.sum_smul, mul_smul],
  rw [← (@equiv.ulift (fin n)).symm.sum_comp, finset.sum_congr rfl],
  rintros j -,
  rw smul_comm, refl,
end

end basic_universal_map

namespace universal_map

variables {m n o : ℕ} (f : universal_map m n) (g : universal_map n o)

def eval_Pow : universal_map m n →+ (Pow m ⋙ F ⟶ Pow n ⋙ F) :=
free_abelian_group.lift $ λ g : basic_universal_map m n, whisker_right g.eval_Pow F

lemma eval_Pow_of (g : basic_universal_map m n) :
  eval_Pow F (free_abelian_group.of g) = whisker_right g.eval_Pow F :=
free_abelian_group.lift.of _ _

@[simp] lemma eval_Pow_zero : eval_Pow F (0 : universal_map m n) = 0 :=
add_monoid_hom.map_zero _

lemma eval_Pow_zero_app (A : 𝒜) : (eval_Pow F (0 : universal_map m n)).app A = 0 :=
by rw [eval_Pow_zero, zero_app]

lemma eval_Pow_comp : eval_Pow F (universal_map.comp g f) = eval_Pow F f ≫ eval_Pow F g :=
begin
  rw [← add_monoid_hom.comp_apply, ← add_monoid_hom.comp_hom_apply_apply,
    ← add_monoid_hom.comp_apply, eq_comm,
    ← category_theory.preadditive.comp_hom_apply_apply, ← add_monoid_hom.flip_apply,
    ← add_monoid_hom.comp_apply, ← add_monoid_hom.comp_hom_apply_apply,
    ← add_monoid_hom.flip_apply _ _ (eval_Pow F),
    ← add_monoid_hom.comp_apply, ← add_monoid_hom.comp_hom_apply_apply,
    ← add_monoid_hom.comp_apply, ← add_monoid_hom.comp_hom_apply_apply],
  congr' 2,
  clear f g,
  ext g f : 2,
  simp only [add_monoid_hom.comp_hom_apply_apply, add_monoid_hom.comp_apply,
    add_monoid_hom.flip_apply, category_theory.preadditive.comp_hom_apply_apply,
    comp_of, eval_Pow_of, whisker_right_comp, basic_universal_map.eval_Pow_comp],
end

lemma eval_Pow_comp_app (A : 𝒜) :
  (eval_Pow F (universal_map.comp g f)).app A = (eval_Pow F f).app A ≫ (eval_Pow F g).app A :=
by rw [eval_Pow_comp, nat_trans.comp_app]

@[simps {fully_applied := ff}]
def eval_Pow_functor : FreeMat ⥤ (𝒜 ⥤ 𝒜) :=
{ obj := λ n, Pow n ⋙ F,
  map := λ m n f, eval_Pow F f,
  map_id' := λ n,
  begin
    refine (eval_Pow_of F _).trans _,
    ext A : 2, dsimp,
    rw ← F.map_id, congr' 1,
    ext i j : 2,
    simp only [biproduct.ι_matrix, category.comp_id, biproduct.lift_π, basic_universal_map.id],
    rw biproduct.ι_π,
    split_ifs with hij,
    { cases hij, rw [matrix.one_apply_eq, one_smul, eq_to_hom_refl], },
    { rw [matrix.one_apply_ne, zero_smul], cases i, cases j, dsimp, rintro rfl, exact hij rfl }
  end,
  map_comp' := λ m n o f g, eval_Pow_comp F _ _ }

instance eval_Pow_functor_additive : (eval_Pow_functor F).additive :=
{ map_zero' := sorry, -- redundant
  map_add' := λ m n f g, by { dsimp [eval_Pow], rw add_monoid_hom.map_add } }

end universal_map

namespace data

open universal_map

def eval_functor : data ⥤ chain_complex (𝒜 ⥤ 𝒜) ℕ :=
(eval_Pow_functor F).map_homological_complex _

def eval_functor.obj (A : 𝒜) : data ⥤ chain_complex 𝒜 ℕ :=
eval_functor F ⋙ homological_complex.functor_eval.obj A

-- @[simps]
-- def eval_functor.obj (M : 𝒜) : chain_complex 𝒜 ℕ :=
-- { X := λ n, (Pow (BD.X n) ⋙ F).obj M,
--   d := λ m n, (eval_Pow F (BD.d m n)).app M,
--   shape' := λ i j h, by rw [BD.shape i j h, universal_map.eval_Pow_zero_app],
--   d_comp_d' := λ i j k hij hjk, begin
--     rw [← universal_map.eval_Pow_comp_app],
--     have := BD.d_comp_d i j k,
--     convert universal_map.eval_Pow_zero_app _ _ using 3,
--   end }

-- @[simps {fully_applied := ff}]
-- def eval_functor : 𝒜 ⥤ chain_complex 𝒜 ℕ :=
-- { obj := eval_functor.obj BD F,
--   map := λ A B f,
--   { f := λ n, (Pow (BD.X n) ⋙ F).map f,
--     comm' := λ m n h, by simp only [eval_functor.obj_d, nat_trans.naturality] },
--   map_id' := λ A, by { ext n, exact category_theory.functor.map_id _ _ },
--   map_comp' := λ A B C f g, by { ext n, exact category_theory.functor.map_comp _ _ _ } }

-- @[simps {fully_applied := ff}]
-- def map_eval_functor {BD₁ BD₂ : data} (φ : BD₁ ⟶ BD₂) :
--   BD₁.eval_functor F ⟶ BD₂.eval_functor F :=
-- { app := λ A,
--   { f := λ i, (universal_map.eval_Pow F (φ.f i)).app A,
--     comm' := by { intros, dsimp only [eval_functor_obj, eval_functor.obj_d],
--       simp only [← nat_trans.comp_app, ← eval_Pow_comp F], congr' 2, apply φ.comm } },
--   naturality' := λ A B f, by { ext i : 2, apply nat_trans.naturality } }

end data

namespace package

open universal_map

variables (BD' : package)

def eval_homotopy := (eval_Pow_functor F).map_homotopy BD'.homotopy

-- #check eval_homotopy F BD'
-- eval_homotopy F BD' :
--  homotopy (((eval_Pow_functor F).map_homological_complex (complex_shape.down ℕ)).map (BD'.data.proj 2))
--    (((eval_Pow_functor F).map_homological_complex (complex_shape.down ℕ)).map (BD'.data.sum 2))

end package

end breen_deligne
