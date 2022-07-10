import breen_deligne.eval

noncomputable theory

namespace breen_deligne

open category_theory category_theory.limits category_theory.category
  category_theory.preadditive

variables {A₁ A₂ A₃ : Type*} [category A₁] [preadditive A₁] [has_finite_biproducts A₁]
  [category A₂] [preadditive A₂] [has_finite_biproducts A₂]
  [category A₃] [preadditive A₃] [has_finite_biproducts A₃]

namespace universal_map

variables {m n : ℕ} (f : universal_map m n)

def eval_Pow' (F : A₁ ⥤ A₂) : universal_map m n →+ (Pow m ⋙ F ⟶ Pow n ⋙ F) :=
free_abelian_group.lift $ λ g : basic_universal_map m n, whisker_right g.eval_Pow F

@[simp]
lemma eval_Pow'_of (F : A₁ ⥤ A₂) (f : basic_universal_map m n) :
  eval_Pow' F (free_abelian_group.of f) = whisker_right f.eval_Pow F :=
free_abelian_group.lift.of _ _

lemma eval_Pow'_hcomp (F : A₁ ⥤ A₂) (H : A₂ ⥤ A₃) [H.additive] :
  eval_Pow' F f ◫ 𝟙 H = eval_Pow' (F ⋙ H) f :=
begin
  revert f,
  let φ : universal_map m n →+ ((Pow m ⋙ F) ⋙ H ⟶ (Pow n ⋙ F) ⋙ H) :=
  { to_fun := λ f, whisker_right (eval_Pow' F f) H,
    map_zero' := by { ext, dsimp, simp only [map_zero, nat_trans.app_zero, functor.map_zero], },
    map_add' := λ f₁ f₂, by { ext, dsimp, simp only [map_add, nat_trans.app_add,
      functor.map_add], }, },
  suffices : φ = eval_Pow' (F ⋙ H),
  { intro f,
    change 𝟙 _ ≫ φ f = _,
    rw [category.id_comp, this], },
  ext1 f,
  simp only [add_monoid_hom.coe_mk, eval_Pow'_of, whisker_right_twice],
end

lemma map_eval_Pow' (F : A₁ ⥤ A₂) (H : A₂ ⥤ A₃) [H.additive] (M₁ : A₁) :
  H.map ((eval_Pow' F f).app M₁) = (eval_Pow' (F ⋙ H) f).app M₁ :=
by simpa only [nat_trans.hcomp_id_app] using nat_trans.congr_app (f.eval_Pow'_hcomp F H) M₁

lemma map_eval_Pow (F : A₁ ⥤ A₁) (H : A₁ ⥤ A₂) [H.additive] (M₁ : A₁) :
  H.map ((eval_Pow F f).app M₁) = (eval_Pow' (F ⋙ H) f).app M₁ :=
map_eval_Pow' f F H M₁

@[reassoc]
lemma congr_eval_Pow' {F F' : A₁ ⥤ A₂} (φ : F ⟶ F') (M₁ : A₁) :
  (eval_Pow' F f).app M₁ ≫ φ.app ((Pow n).obj M₁) =
  φ.app ((Pow m).obj M₁) ≫ (eval_Pow' F' f).app M₁ :=
begin
  revert f,
  let φ₁ : universal_map m n →+ ((Pow m ⋙ F).obj M₁ ⟶ (Pow n ⋙ F').obj M₁) :=
  { to_fun := λ f, (eval_Pow' F f).app M₁ ≫ φ.app ((Pow n).obj M₁),
    map_zero' := by simp only [map_zero, nat_trans.app_zero, zero_comp],
    map_add' := λ f₁ f₂, by simp only [map_add, nat_trans.app_add, add_comp], },
  let φ₂ : universal_map m n →+ ((Pow m ⋙ F).obj M₁ ⟶ (Pow n ⋙ F').obj M₁) :=
  { to_fun := λ f, φ.app ((Pow m).obj M₁) ≫ (eval_Pow' F' f).app M₁,
    map_zero' := by simp only [map_zero, nat_trans.app_zero, comp_zero],
    map_add' := λ f₁ f₂, by simp only [map_add, nat_trans.app_add, comp_add], },
  suffices : φ₁ = φ₂,
  { intro f,
    change φ₁ f = φ₂ f,
    rw this, },
  ext,
  dsimp only [φ₁, φ₂],
  simp only [add_monoid_hom.coe_mk, eval_Pow'_of, whisker_right_app, nat_trans.naturality],
end

end universal_map

end breen_deligne
