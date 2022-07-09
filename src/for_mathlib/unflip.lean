import category_theory.functor.category

open category_theory

namespace category_theory

namespace nat_trans

@[simps]
def unflip {C D E : Type*} [category C] [category D] [category E]
  {F G : C ⥤ D ⥤ E} (φ : F.flip ⟶ G.flip) : F ⟶ G :=
{ app := λ c,
  { app := λ d, (φ.app d).app c,
    naturality' := λ d₁ d₂ g, nat_trans.congr_app (φ.naturality g) c, },
  naturality' := λ c₁ c₂ f, begin
    ext d,
    exact (φ.app d).naturality f,
  end}

def unflip_id {C D E : Type*} [category C] [category D] [category E]
  {F : C ⥤ D ⥤ E} : nat_trans.unflip (𝟙 F.flip) = 𝟙 F := rfl

def unflip_comp {C D E : Type*} [category C] [category D] [category E]
  {F G H : C ⥤ D ⥤ E} (φ₁ : F.flip ⟶ G.flip) (φ₂ : G.flip ⟶ H.flip) :
  nat_trans.unflip (φ₁ ≫ φ₂) = nat_trans.unflip φ₁ ≫ nat_trans.unflip φ₂ := rfl

end nat_trans

namespace nat_iso

def unflip {C D E : Type*} [category C] [category D] [category E]
  {F G : C ⥤ D ⥤ E} (e : F.flip ≅ G.flip) : F ≅ G :=
{ hom := nat_trans.unflip e.hom,
  inv := nat_trans.unflip e.inv,
  hom_inv_id' := by rw [← nat_trans.unflip_comp, e.hom_inv_id, nat_trans.unflip_id],
  inv_hom_id' := by rw [← nat_trans.unflip_comp, e.inv_hom_id, nat_trans.unflip_id], }

end nat_iso

end category_theory
