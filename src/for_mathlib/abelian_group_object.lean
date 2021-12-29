import category_theory.limits.shapes.binary_products
import category_theory.monoidal.CommMon_
import category_theory.monoidal.of_chosen_finite_products
import category_theory.limits.types
import algebra.category.Group
import category_theory.sites.sheaf_of_types

namespace category_theory
open category_theory.limits category_theory.monoidal_category

universes w v u
variables {C : Type u} [category.{v} C] (T : grothendieck_topology C)

noncomputable theory

namespace SheafOfTypes

@[simps]
def terminal_sheaf : SheafOfTypes.{w} T :=
{ val := (functor.const _).obj punit,
  cond := sorry }

def terminal_cone : cone (functor.empty (SheafOfTypes.{w} T)) :=
{ X := terminal_sheaf T,
  π := { app := λ X, X.elim } }

variables {T}
def terminal_sheaf.to (F : SheafOfTypes.{w} T) : F ⟶ terminal_sheaf T :=
⟨{ app := λ X t, punit.star }⟩
variables (T)

def terminal_cone_is_limit : is_limit (terminal_cone T) :=
{ lift := λ S, terminal_sheaf.to _ }

variables {T}

@[simps]
def product_sheaf (F G : SheafOfTypes.{w} T) : SheafOfTypes.{w} T :=
{ val :=
  { obj := λ X, F.val.obj X × G.val.obj X,
    map := λ X Y f t, (F.val.map f t.1, G.val.map f t.2) },
  cond := sorry }

@[simps]
def product_sheaf.swap (F G : SheafOfTypes.{w} T) : product_sheaf F G ≅ product_sheaf G F :=
{ hom := ⟨{ app := λ X, _root_.prod.swap }⟩,
  inv := ⟨{ app := λ X, _root_.prod.swap }⟩ }

@[simps]
def product_sheaf.fst (F G : SheafOfTypes.{w} T) : product_sheaf F G ⟶ F :=
⟨{ app := λ X, _root_.prod.fst }⟩

@[simps]
def product_sheaf.snd (F G : SheafOfTypes.{w} T) : product_sheaf F G ⟶ G :=
⟨{ app := λ X, _root_.prod.snd }⟩

@[simps]
def product_cone (F G : SheafOfTypes.{w} T) : binary_fan F G :=
binary_fan.mk (product_sheaf.fst F G) (product_sheaf.snd F G)

@[simps]
def product_sheaf.lift {F G H : SheafOfTypes.{w} T} (f : H ⟶ F) (g : H ⟶ G) :
  H ⟶ product_sheaf F G :=
⟨{ app := λ X t, (f.val.app X t, g.val.app X t),
  naturality' := begin
    intros X Y e,
    ext t,
    { change (H.val.map e ≫ f.val.app Y) t = _,
      rw f.val.naturality,
      simp only [product_sheaf_val_map, types_comp_apply] },
    { change (H.val.map e ≫ g.val.app Y) t = _,
      rw g.val.naturality,
      simp only [product_sheaf_val_map, types_comp_apply], },
  end }⟩

@[simps]
def product_cone_is_limit (F G : SheafOfTypes.{w} T) : is_limit (product_cone F G) :=
{ lift := λ (S : binary_fan F G), product_sheaf.lift S.fst S.snd,
  fac' := begin
    rintros S (j|j),
    tidy,
  end,
  uniq' := begin
    intros S m h,
    ext X t : 5,
    { specialize h walking_pair.left,
      dsimp,
      apply_fun (λ e, e.val.app X t) at h,
      exact h },
    { specialize h walking_pair.right,
      dsimp,
      apply_fun (λ e, e.val.app X t) at h,
      exact h },
  end }

variables (T)

instance : monoidal_category (SheafOfTypes.{w} T) :=
monoidal_of_chosen_finite_products ⟨terminal_cone T, terminal_cone_is_limit T⟩
  (λ F G, ⟨product_cone F G, product_cone_is_limit F G⟩)

instance : braided_category (SheafOfTypes.{w} T) :=
{ braiding := λ X Y, product_sheaf.swap X Y }

structure Group extends Mon_ (SheafOfTypes.{w} T) :=
(inv : X ⟶ X)
(inv_mul : (product_sheaf.lift inv (𝟙 X)) ≫ mul = terminal_sheaf.to _ ≫ one)
(mul_inv : (product_sheaf.lift (𝟙 X) inv) ≫ mul = terminal_sheaf.to _ ≫ one)

structure Ab extends CommMon_ (SheafOfTypes.{w} T) :=
(inv : X ⟶ X)
(inv_mul : (product_sheaf.lift inv (𝟙 X)) ≫ mul = terminal_sheaf.to _ ≫ one)
(mul_inv : (product_sheaf.lift (𝟙 X) inv) ≫ mul = terminal_sheaf.to _ ≫ one)

end SheafOfTypes

end category_theory
