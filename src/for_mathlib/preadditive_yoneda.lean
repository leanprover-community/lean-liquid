import category_theory.preadditive.yoneda

open opposite

namespace category_theory

universes v u
variables (A : Type u) [category.{v} A] [preadditive A]

lemma is_iso_of_is_iso_preadditive_yoneda_map_app {X Y : A}
  (f : X ⟶ Y) [∀ W : A, is_iso ((preadditive_yoneda.map f).app (op W))] :
  is_iso f :=
begin
  let e := (preadditive_yoneda.map f).app (op Y),
  let g := (preadditive_yoneda.map f).app (op X),
  use inv e (𝟙 _),
  split,
  { apply_fun g,
    swap,
    { intros i j h,
      apply_fun inv g at h,
      simpa only [← comp_apply, is_iso.hom_inv_id] using h },
    dsimp [g],
    simp only [category.id_comp, category.assoc],
    change f ≫ e _ = _,
    simp only [← comp_apply, is_iso.hom_inv_id],
    simp },
  { change e (inv e (𝟙 _)) = _,
    simp only [← comp_apply, is_iso.inv_hom_id],
    simpa },
end

end category_theory
