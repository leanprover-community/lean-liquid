import category_theory.limits.shapes.products
import category_theory.over
import algebraic_topology.simplicial_object
import category_theory.products.basic

noncomputable theory

namespace category_theory

universes v u

variables {C : Type u} [category.{v} C] {X : C}

namespace limits
-- TODO: Move this section to mathlib!

@[ext]
lemma pi_ext {α : Type v} (f : α → C) [limits.has_product f] (gs : Π (a : α), X ⟶ f a)
  (g : X ⟶ ∏ f) : (∀ a : α, gs a = g ≫ limits.pi.π _ _) → limits.pi.lift gs = g :=
begin
  intro h,
  symmetry,
  apply (limit.is_limit _).uniq (fan.mk X gs),
  intros a,
  symmetry,
  apply h,
end

end limits

namespace cech

abbreviation ufin (n : ℕ) := ulift (fin n)
abbreviation ufin.up {n} : fin n → ufin n := _root_.ulift.up
abbreviation ufin.map {m n} (f : fin m → fin n) : ufin m → ufin n :=
λ i, ufin.up $ f i.down

local attribute [semireducible] simplex_category.hom

variable (X)

@[simps]
def cech_obj [∀ (n : ℕ), limits.has_product (λ i : ufin (n+1), X)] :
  simplicial_object C :=
{ obj := λ x, ∏ (λ i : ufin (x.unop.len+1), X),
  map := λ x y f, limits.pi.lift $ λ i, limits.pi.π _ $ ufin.map f.unop.to_preorder_hom i }.

open_locale simplicial

-- left adjoint, but it's a bit annoying to prove
-- as some API is missing from opposite.op and from simplicial stuff
@[simps]
def base : simplicial_object C ⥤ C :=
(evaluation _ _).obj (opposite.op [0])

/-
def cech_equiv [∀ (n : ℕ), limits.has_product (λ i : ufin (n+1), X)] (Y : simplicial_object C) :
  (Y ⟶ cech_obj X) ≃ (base.obj Y ⟶ X) :=
{ to_fun := λ f, base.map f ≫ limits.pi.π _ (ufin.up 0),
  inv_fun := λ f,
  { app := λ x, limits.pi.lift (λ i, Y.map (_) ≫ f),
    naturality' := _ },
  left_inv := _,
  right_inv := _ }
-/

@[simps]
def cech [∀ (n : ℕ), limits.has_products_of_shape (ufin (n+1)) C] :
  C ⥤ simplicial_object C :=
{ obj := λ X, cech_obj X,
  map := λ X Y f,
  { app := λ x, limits.pi.map (λ _, f) } }.

--def adjunction [∀ (n : ℕ), limits.has_products_of_shape (ufin (n+1)) C] :
--  base ⊣ (cech : C ⥤ _) :=

end cech

end category_theory
