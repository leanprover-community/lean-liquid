import for_mathlib.endomorphisms.basic
import for_mathlib.derived.les_facts

noncomputable theory

universes v u

open category_theory category_theory.limits opposite
open bounded_homotopy_category

namespace homological_complex

variables {𝓐 : Type u} [category.{v} 𝓐] [abelian 𝓐]
variables {ι : Type*} {c : complex_shape ι}

def e (X : homological_complex (endomorphisms 𝓐) c) :
  End (((endomorphisms.forget 𝓐).map_homological_complex c).obj X) :=
{ f := λ i, (X.X i).e,
  comm' := λ i j hij, (X.d i j).comm }

end homological_complex

namespace homotopy_category

variables {𝓐 : Type u} [category.{v} 𝓐] [abelian 𝓐]
variables {𝓑 : Type*} [category 𝓑] [abelian 𝓑]
variables (F : 𝓐 ⥤ 𝓑) [functor.additive F]

instance map_homotopy_category_is_bounded_above
  (X : homotopy_category 𝓐 $ complex_shape.up ℤ) [X.is_bounded_above] :
  ((F.map_homotopy_category _).obj X).is_bounded_above :=
sorry

end homotopy_category

namespace bounded_homotopy_category

variables {𝓐 : Type u} [category.{v} 𝓐] [abelian 𝓐]

variables (X : bounded_homotopy_category (endomorphisms 𝓐))

def unEnd : bounded_homotopy_category 𝓐 :=
of $ ((endomorphisms.forget _).map_homotopy_category _).obj X.val

def e : End X.unEnd := (homotopy_category.quotient _ _).map $ X.val.as.e

end bounded_homotopy_category

namespace category_theory

namespace endomorphisms

variables {𝓐 : Type u} [category.{v} 𝓐] [abelian 𝓐] [enough_projectives 𝓐]
variables [has_coproducts_of_shape (ulift.{v} ℕ) 𝓐]

lemma Ext_is_zero_iff (X Y : bounded_homotopy_category (endomorphisms 𝓐)) (i : ℤ) :
  is_zero (((Ext i).obj (op $ X)).obj $ Y) ↔
  (is_iso $ ((Ext i).map (quiver.hom.op X.e)).app Y.unEnd - ((Ext i).obj (op X.unEnd)).map Y.e) :=
begin
  sorry
end

def single_unEnd (X : endomorphisms 𝓐) : ((single _ 0).obj X).unEnd ≅ (single _ 0).obj X.X :=
sorry

lemma single_unEnd_e (X : endomorphisms 𝓐) :
  (single_unEnd X).hom ≫ (single _ 0).map X.e = ((single _ 0).obj X).e ≫ (single_unEnd X).hom :=
sorry

lemma single_e (X : endomorphisms 𝓐) :
  (single_unEnd X).hom ≫ (single _ 0).map X.e ≫ (single_unEnd X).inv = ((single _ 0).obj X).e :=
by rw [← category.assoc, iso.comp_inv_eq, single_unEnd_e]

open category_theory.preadditive

lemma Ext'_is_zero_iff (X Y : endomorphisms 𝓐) (i : ℤ) :
  is_zero (((Ext' i).obj (op X)).obj Y) ↔
  (is_iso $ ((Ext' i).map X.e.op).app Y.X - ((Ext' i).obj (op X.X)).map Y.e) :=
begin
  refine (Ext_is_zero_iff ((single _ 0).obj X) ((single _ 0).obj Y) i).trans _,
  rw [← single_e X, ← single_e Y],
  simp only [category_theory.functor.map_comp, nat_trans.comp_app, op_comp, comp_sub, sub_comp],
  -- delta Ext', dsimp,
  sorry
end

lemma Ext'_is_zero_iff' (X Y : 𝓐) (f : X ⟶ X) (g : Y ⟶ Y) (i : ℤ) :
  is_zero (((Ext' i).obj (op $ endomorphisms.mk X f)).obj $ endomorphisms.mk Y g) ↔
  (is_iso $ ((Ext' i).map f.op).app _ - ((Ext' i).obj _).map g) :=
Ext'_is_zero_iff _ _ _

end endomorphisms

end category_theory
