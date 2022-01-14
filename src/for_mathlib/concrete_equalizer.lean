import category_theory.limits.concrete_category

universes v u

open category_theory

namespace category_theory.limits

local attribute [instance] concrete_category.has_coe_to_fun concrete_category.has_coe_to_sort

variables {C : Type u} [category.{v} C] [concrete_category.{v} C]

section equalizer

lemma concrete.equalizer_ext {X Y : C} (f g : X ⟶ Y) [has_equalizer f g]
  [preserves_limit (parallel_pair f g) (forget C)] (x y : equalizer f g)
  (h : equalizer.ι f g x = equalizer.ι f g y) : x = y :=
begin
  apply concrete.limit_ext,
  rintros (a|a),
  { apply h },
  { rw [← limit.w (parallel_pair f g) walking_parallel_pair_hom.right,
    comp_apply, comp_apply, h] }
end

def concrete.equalizer_equiv_aux {X Y : C} (f g : X ⟶ Y) :
  (parallel_pair f g ⋙ forget C).sections ≃ { x : X // f x = g x } :=
{ to_fun := λ x, ⟨x.1 walking_parallel_pair.zero, begin
    have h1 := x.2 walking_parallel_pair_hom.left,
    have h2 := x.2 walking_parallel_pair_hom.right,
    dsimp at h1 h2,
    erw [h1, h2],
  end⟩,
  inv_fun := λ x,
  { val := λ j,
    match j with
    | walking_parallel_pair.zero := x.1
    | walking_parallel_pair.one := f x.1
    end,
    property := begin
      dsimp [functor.sections],
      rintros (a|a) (b|b) (f|f),
      { simp, },
      { refl },
      { exact x.2.symm },
      { simp },
    end },
  left_inv := begin
    rintros ⟨x,hx⟩,
    ext (a|a),
    { refl },
    { change _ = x _,
      rw ← hx walking_parallel_pair_hom.left,
      refl }
  end,
  right_inv := by { rintros ⟨_,_⟩, ext, refl } }

noncomputable
def concrete.equalizer_equiv {X Y : C} (f g : X ⟶ Y) [has_equalizer f g]
  [preserves_limit (parallel_pair f g) (forget C)] :
  ↥(equalizer f g) ≃ { x // f x = g x } :=
let h1 := limit.is_limit (parallel_pair f g),
    h2 := is_limit_of_preserves (forget C) h1,
    E := h2.cone_point_unique_up_to_iso (types.limit_cone_is_limit _) in
E.to_equiv.trans $ concrete.equalizer_equiv_aux _ _

end equalizer

end category_theory.limits
