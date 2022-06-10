import category_theory.abelian.homology

namespace category_theory

universes v v' u u'
variables {A : Type u} {B : Type u'} [category.{v} A] [category.{v'} B]
  [abelian A] [abelian B] (F : A ⥤ B) [functor.additive F]

namespace functor

open category_theory.limits

class exact : Prop :=
(cond [] : ∀ {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z), exact f g → exact (F.map f) (F.map g))

variables [exact F]

noncomputable theory

def cokernel_comparison {X Y : A} (f : X ⟶ Y) :
  cokernel (F.map f) ⟶ F.obj (cokernel f) :=
cokernel.desc _ (F.map $ cokernel.π _) $
  by rw [← F.map_comp, limits.cokernel.condition, F.map_zero]

instance {X Y : A} (f : X ⟶ Y)  : is_iso (F.cokernel_comparison f) := sorry

def kernel_comparison {X Y : A} (f : X ⟶ Y) :
  F.obj (kernel f) ⟶ kernel (F.map f) :=
kernel.lift _ (F.map $ kernel.ι _) $
  by rw [← F.map_comp, limits.kernel.condition, F.map_zero]

instance {X Y : A} (f : X ⟶ Y) : is_iso (F.kernel_comparison f) := sorry

def map_homology_iso {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) (w w') :
  F.obj (homology f g w) ≅ homology (F.map f) (F.map g) w' :=
{ hom := homology.lift _ _ _ (F.map (homology.ι _ _ _) ≫
    category_theory.inv (F.cokernel_comparison _)) sorry,
  inv := homology.desc' _ _ _ (category_theory.inv (F.kernel_comparison _) ≫
    F.map (homology.π' _ _ _)) sorry,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }

end functor

end category_theory
