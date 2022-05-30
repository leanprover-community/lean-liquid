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

-- def to_endoms : homological_complex (endomorphisms 𝓐) c ⥤ endomorphisms (homological_complex 𝓐 c) :=
-- { obj := λ X, ⟨((endomorphisms.forget _).map_homological_complex _).obj X, _⟩,
--   map := _,
--   map_id' := _,
--   map_comp' := _ }

end homological_complex

namespace category_theory

namespace endomorphisms

variables {𝓐 : Type u} [category.{v} 𝓐] [abelian 𝓐] [enough_projectives 𝓐]
variables [has_coproducts_of_shape (ulift.{v} ℕ) 𝓐]

lemma Ext_is_zero_iff (X : chain_complex (endomorphisms 𝓐) ℕ) (Y : endomorphisms 𝓐) (i : ℤ) :
  is_zero (((Ext i).obj
    (op $ chain_complex.to_bounded_homotopy_category.obj X)).obj $
    (single _ 0).obj Y) ↔
  (is_iso $
    ((Ext i).map
      ((chain_complex.to_bounded_homotopy_category).map $ homological_complex.e X).op).app
      ((single _ 0).obj Y.X) -
    ((Ext i).obj
      (op $ ((endomorphisms.forget _).map_homological_complex _ ⋙
          chain_complex.to_bounded_homotopy_category).obj X)
      ).map ((single _ 0).map Y.e)) :=
begin
  sorry
end

def aux (X : endomorphisms 𝓐) :
  (single (endomorphisms 𝓐) 0).op.obj (op X) ≅
    op (chain_complex.to_bounded_homotopy_category.obj
       ((homological_complex.single (endomorphisms 𝓐) (complex_shape.down ℕ) 0).obj X)) :=
sorry

lemma Ext'_is_zero_iff (X Y : endomorphisms 𝓐) (i : ℤ) :
  is_zero (((Ext' i).obj (op X)).obj Y) ↔
  (is_iso $ ((Ext' i).map X.e.op).app Y.X - ((Ext' i).obj (op X.X)).map Y.e) :=
begin
  delta Ext',
  have := Ext_is_zero_iff ((homological_complex.single _ _ 0).obj X) Y i,
  convert this using 1; clear this; apply propext,
  { apply iso.is_zero_iff, refine ((Ext i).flip.obj _).map_iso (aux X), },
  sorry
end

lemma Ext'_is_zero_iff' (X Y : 𝓐) (f : X ⟶ X) (g : Y ⟶ Y) (i : ℤ) :
  is_zero (((Ext' i).obj (op $ endomorphisms.mk X f)).obj $ endomorphisms.mk Y g) ↔
  (is_iso $ ((Ext' i).map f.op).app _ - ((Ext' i).obj _).map g) :=
Ext'_is_zero_iff _ _ _

end endomorphisms

end category_theory
