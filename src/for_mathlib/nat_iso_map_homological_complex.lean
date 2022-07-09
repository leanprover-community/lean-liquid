import algebra.homology.additive

namespace category_theory

open category

def nat_iso.map_homological_complex {ι V W : Type*}
  [category V] [category W] [preadditive V] [preadditive W] {F G : V ⥤ W}
  [F.additive] [G.additive]
  (e : F ≅ G) (c : complex_shape ι) :
    F.map_homological_complex c ≅ G.map_homological_complex c :=
{ hom := nat_trans.map_homological_complex e.hom c,
  inv := nat_trans.map_homological_complex e.inv c,
  hom_inv_id' := by { ext X i, dsimp, simp only [iso.hom_inv_id_app], },
  inv_hom_id' := by { ext X i, dsimp, simp only [iso.inv_hom_id_app], }, }

end category_theory
