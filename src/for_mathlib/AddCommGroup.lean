import algebra.category.Module.adjunctions
import group_theory.free_abelian_group_finsupp
import algebra.category.Group.adjunctions

open category_theory

namespace AddCommGroup

noncomputable theory
universe u

@[simps]
def free' : Type u ⥤ AddCommGroup.{u} :=
{ obj := λ X, AddCommGroup.of $ X →₀ ℤ,
  map := λ X Y f, finsupp.map_domain.add_monoid_hom f,
  map_id' := begin
    intros X, ext, dsimp, simp,
  end,
  map_comp' := begin
    intros X Y Z f g, ext, dsimp, simp,
  end } .

@[simps]
def of_iso {A B : Type u} [add_comm_group A] [add_comm_group B]
  (e : A ≃+ B) : of A ≅ of B :=
{ hom := e.to_add_monoid_hom,
  inv := e.symm.to_add_monoid_hom,
  hom_inv_id' := begin
    ext, dsimp, simp,
  end,
  inv_hom_id' := begin
    ext, dsimp, simp,
  end } .

@[simps]
def free_iso_free' : free.{u} ≅ free'.{u} :=
category_theory.nat_iso.of_components
(λ X, of_iso (free_abelian_group.equiv_finsupp X))
begin
  intros X Y f, ext, dsimp, simp,
end

def adj' : free'.{u} ⊣ forget AddCommGroup.{u} :=
AddCommGroup.adj.of_nat_iso_left $ free_iso_free'.{u}

end AddCommGroup
