import for_mathlib.endomorphisms.basic
import for_mathlib.derived.les_facts
import for_mathlib.additive_functor

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

def mk_end (X : homological_complex 𝓐 c) (f : X ⟶ X) :
  homological_complex (endomorphisms 𝓐) c :=
{ X := λ i, ⟨X.X i, f.f i⟩,
  d := λ i j, ⟨X.d i j, f.comm i j⟩,
  shape' := by { intros i j h, ext, apply X.shape i j h },
  d_comp_d' := by { intros, ext, apply X.d_comp_d } }

end homological_complex

namespace homotopy_category

variables {𝓐 : Type u} [category.{v} 𝓐] [abelian 𝓐]
variables {𝓑 : Type*} [category 𝓑] [abelian 𝓑]
variables (F : 𝓐 ⥤ 𝓑) [functor.additive F]

instance map_homotopy_category_is_bounded_above
  (X : homotopy_category 𝓐 $ complex_shape.up ℤ) [X.is_bounded_above] :
  ((F.map_homotopy_category _).obj X).is_bounded_above :=
begin
  obtain ⟨b, hb⟩ := is_bounded_above.cond X,
  exact ⟨⟨b, λ i hi, category_theory.functor.map_is_zero _ (hb i hi)⟩⟩,
 end

end homotopy_category

namespace bounded_homotopy_category

variables {𝓐 : Type u} [category.{v} 𝓐] [abelian 𝓐]
variables [has_coproducts_of_shape (ulift.{v} ℕ) 𝓐]
variables [has_products_of_shape (ulift.{v} ℕ) 𝓐]

variables (X : bounded_homotopy_category (endomorphisms 𝓐))

/-- `unEnd` is the "forget the endomorphism" map from the category whose objects are complexes
of pairs `(Aⁱ,eⁱ)` with morphisms defined up to homotopy, to the category whose objects are
complexes of objects `Aⁱ` with morphisms defined up to homotopy.  -/
def unEnd : bounded_homotopy_category 𝓐 :=
of $ ((endomorphisms.forget _).map_homotopy_category _).obj X.val

def e : End X.unEnd := (homotopy_category.quotient _ _).map $ X.val.as.e

end bounded_homotopy_category

namespace category_theory

section
variables {C : Type*} [category C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)

lemma is_iso.comp_right_iff [is_iso g] : is_iso (f ≫ g) ↔ is_iso f :=
begin
  split; introI h,
  { have : is_iso ((f ≫ g) ≫ inv g), { apply_instance },
    simpa only [category.assoc, is_iso.hom_inv_id, category.comp_id] },
  { apply_instance }
end

lemma is_iso.comp_left_iff [is_iso f] : is_iso (f ≫ g) ↔ is_iso g :=
begin
  split; introI h,
  { have : is_iso (inv f ≫ (f ≫ g)), { apply_instance },
    simpa only [category.assoc, is_iso.inv_hom_id_assoc] },
  { apply_instance }
end

end

namespace endomorphisms

variables {𝓐 : Type u} [category.{v} 𝓐] [abelian 𝓐] [enough_projectives 𝓐]
variables [has_coproducts_of_shape (ulift.{v} ℕ) 𝓐]
variables [has_products_of_shape (ulift.{v} ℕ) 𝓐]

def mk_bo_ho_ca' (X : cochain_complex 𝓐 ℤ)
  [((homotopy_category.quotient 𝓐 (complex_shape.up ℤ)).obj X).is_bounded_above] (f : X ⟶ X) :
  bounded_homotopy_category (endomorphisms 𝓐) :=
{ val := { as :=
  { X := λ i, ⟨X.X i, f.f i⟩,
    d := λ i j, ⟨X.d i j, f.comm _ _⟩,
    shape' := λ i j h, by { ext, exact X.shape i j h, },
    d_comp_d' := λ i j k hij hjk, by { ext, apply homological_complex.d_comp_d } } },
  bdd := begin
    obtain ⟨a, ha⟩ := homotopy_category.is_bounded_above.cond ((homotopy_category.quotient 𝓐 (complex_shape.up ℤ)).obj X),
    refine ⟨⟨a, λ i hi, _⟩⟩,
    rw is_zero_iff_id_eq_zero, ext, dsimp, rw ← is_zero_iff_id_eq_zero,
    exact ha i hi,
  end }

def mk_bo_ho_ca (X : bounded_homotopy_category 𝓐) (f : X ⟶ X) :
  bounded_homotopy_category (endomorphisms 𝓐) :=
@mk_bo_ho_ca' _ _ _ _ _ _ X.val.as (by { cases X with X hX, cases X, exact hX }) f.out
.

lemma quot_out_single_map {X Y : 𝓐} (f : X ⟶ Y) (i : ℤ) :
  ((homotopy_category.single 𝓐 i).map f).out = (homological_complex.single 𝓐 _ i).map f :=
begin
  have h := homotopy_category.homotopy_out_map
    ((homological_complex.single 𝓐 (complex_shape.up ℤ) i).map f),
  ext k,
  erw h.comm k,
  suffices : (d_next k) h.hom + (prev_d k) h.hom = 0, { rw [this, zero_add] },
  obtain (hki|rfl) := ne_or_eq k i,
  { apply limits.is_zero.eq_of_src,
    show is_zero (ite (k = i) X _), rw [if_neg hki], apply is_zero_zero },
  { have hk1 : (complex_shape.up ℤ).rel (k-1) k := sub_add_cancel _ _,
    have hk2 : (complex_shape.up ℤ).rel k (k+1) := rfl,
    rw [prev_d_eq _ hk1, d_next_eq _ hk2],
    have aux1 : h.hom (k + 1) k = 0,
    { apply limits.is_zero.eq_of_src, show is_zero (ite _ X _), rw if_neg, apply is_zero_zero,
      linarith },
    have aux2 : h.hom k (k - 1) = 0,
    { apply limits.is_zero.eq_of_tgt, show is_zero (ite _ Y _), rw if_neg, apply is_zero_zero,
      linarith },
    rw [aux1, aux2, comp_zero, zero_comp, add_zero], }
end

def mk_bo_ha_ca'_single (X : 𝓐) (f : X ⟶ X) :
  mk_bo_ho_ca' ((homological_complex.single _ _ 0).obj X) (functor.map _ f) ≅ (single _ 0).obj ⟨X, f⟩ :=
bounded_homotopy_category.mk_iso
begin
  refine (homotopy_category.quotient _ _).map_iso _,
  refine homological_complex.hom.iso_of_components _ _,
  { intro i,
    refine endomorphisms.mk_iso _ _,
    { dsimp, split_ifs, { exact iso.refl _ },
      { refine (is_zero_zero _).iso _, apply endomorphisms.is_zero_X,
        exact is_zero_zero (endomorphisms 𝓐), } },
    { dsimp, split_ifs with hi,
      { subst i, dsimp, erw [iso.refl_hom], simp only [category.id_comp, category.comp_id],
        convert rfl, },
      { apply is_zero.eq_of_src, rw [if_neg hi], exact is_zero_zero _ } } },
  { rintro i j (rfl : _ = _),
    by_cases hi : i = 0,
    { apply is_zero.eq_of_tgt, dsimp, rw [if_neg], exact is_zero_zero _, linarith only [hi] },
    { apply is_zero.eq_of_src, dsimp, rw [is_zero_iff_id_eq_zero], ext, dsimp, rw [if_neg hi],
      apply (is_zero_zero _).eq_of_src } }
end

def mk_bo_ha_ca_single (X : 𝓐) (f : X ⟶ X) :
  mk_bo_ho_ca ((single _ 0).obj X) ((single _ 0).map f) ≅ (single _ 0).obj ⟨X, f⟩ :=
bounded_homotopy_category.mk_iso
begin
  dsimp only [mk_bo_ho_ca, single],
  refine (homotopy_category.quotient _ _).map_iso _,
  refine homological_complex.hom.iso_of_components _ _,
  { intro i,
    refine endomorphisms.mk_iso _ _,
    { dsimp, split_ifs, { exact iso.refl _ },
      { refine (is_zero_zero _).iso _, apply endomorphisms.is_zero_X,
        exact is_zero_zero (endomorphisms 𝓐), } },
    { dsimp, erw quot_out_single_map, dsimp, split_ifs with hi,
      { subst i, dsimp, erw [iso.refl_hom], simp only [category.id_comp, category.comp_id],
        convert rfl, },
      { apply is_zero.eq_of_src, rw [if_neg hi], exact is_zero_zero _ } } },
  { rintro i j (rfl : _ = _),
    by_cases hi : i = 0,
    { apply is_zero.eq_of_tgt, dsimp, rw [if_neg], exact is_zero_zero _, linarith only [hi] },
    { apply is_zero.eq_of_src, dsimp, rw [is_zero_iff_id_eq_zero], ext, dsimp, rw [if_neg hi],
      apply (is_zero_zero _).eq_of_src } }
end
.

/-

Mathematical summary of the `Ext_is_zero_iff` `sorry` according to kmb's
possibly flawed understanding:

The lemma will follow from the following things:

1) If X is a complex in the bounded homotopy category
and Y is an object, thought of as a `single`
complex, then Extⁱ(X,Y) is the homology of the complex
(Cᵢ) whose i'th term is Hom(Pⁱ,Y), where P is a projective
replacement of X. This applies to both the category 𝓐
and to the endomorphism category.

2) For a cleverly chosen choice of Pⁱ (see `exists_K_projective_endomorphism_replacement`)
we have a short exact sequence of complexes
0 -> Hom_{endos}(Pⁱ,Y) -> Hom(Pⁱ,Y) -> Hom(Pⁱ,Y)->0
where the surjection is e(P) - e(Y), with e the endomorphism.
This can be checked to be surjective via an explicit construction;
the trick is that Pⁱ is going to be `free Q` for some object `Q : 𝓐`

-/
-- This is an approximation of the statement we need
-- for Pⁱ. Hopefully this is what we need. I might need
-- to add extra things, hopefully not, but let's see
-- if it's enough to prove `Ext_is_zero_iff`.
-- Question: does `projective Q` imply `projective (free Q)`?
-- Adam says we have this in `endomorphisms/basic`.
lemma exists_K_projective_endomorphism_replacement
  (X : bounded_homotopy_category (endomorphisms 𝓐)) :
∃ (P : bounded_homotopy_category (endomorphisms 𝓐))
  [homotopy_category.is_K_projective P.val]
  (f : P ⟶ X), homotopy_category.is_quasi_iso f
  ∧ (∀ j, ∃ Q, projective Q ∧ ∃ (i: P.val.as.X j ≅ free Q), true)
--  ∧ ∀ k, projective (P.val.as.X k) -- should follow
--  ∧ ∀ k, projective (P.val.as.X k).X -- should follow
:= sorry

/-

Idea : We need a short exact sequence of complexes as above, and then
the below follows from the associated long exact sequence
of cohomology.

-/

lemma Ext_is_zero_iff (X : chain_complex 𝓐 ℕ) (Y : 𝓐)
  (f : X ⟶ X) (g : Y ⟶ Y) :
  (∀ i, is_zero (((Ext i).obj (op $ chain_complex.to_bounded_homotopy_category.obj (X.mk_end f))).obj $ (single _ 0).obj ⟨Y, g⟩)) ↔
  (∀ i, is_iso $ ((Ext i).map (chain_complex.to_bounded_homotopy_category.map f).op).app _ -
                 ((Ext i).obj (op _)).map ((single _ 0).map g)) :=
begin
  sorry,
end

-- this is an older version; there might be a couple of useful
-- things here. The first line is not right though, we can't
-- use `exists_K_projective_replacement`, the idea is
-- to use `exists_K_projective_endomorphism_replacement` instead.
/-
lemma Ext_is_zero_iff' (X Y : bounded_homotopy_category (endomorphisms 𝓐)) :
  (∀ i, is_zero (((Ext i).obj (op $ X)).obj $ Y)) ↔
  (∀ i, is_iso $
    ((Ext i).map (quiver.hom.op X.e)).app Y.unEnd - ((Ext i).obj (op X.unEnd)).map Y.e) :=
begin
  -- update: this proof plan might well not work.
  -- this might be refactored out
  obtain ⟨P, _inst, f, h1, h2⟩ := exists_K_projective_replacement X.unEnd,
  resetI,
  let fP := (functor.map_homological_complex (functor.free 𝓐) (complex_shape.up ℤ)).obj P.val.as,
  obtain ⟨N, hN⟩ := P.bdd,
  have hN' : ∀ (i : ℤ), N ≤ i →
    is_zero (((homotopy_category.quotient (endomorphisms 𝓐) (complex_shape.up ℤ)).obj fP).as.X i),
  { exact λ i hNi, (functor.free 𝓐).map_is_zero (hN i hNi), },
  have hfPbdd : homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj fP),
  { exact ⟨⟨N, hN'⟩⟩, },
  haveI hproj : ∀ i, projective (fP.X i),
  { intro i,
    apply free.projective, },
  let fP' : bounded_homotopy_category (endomorphisms 𝓐) :=
    { val := (homotopy_category.quotient _ _).obj fP,
      bdd := hfPbdd },

  /-
  * Then use an argument similar to the proof of this lemma
    https://github.com/leanprover-community/lean-liquid/blob/0e192c63da9d578301d4ca75c778abe342f7474f/src/for_mathlib/derived/lemmas.lean#L536
    to see that the complex you have obtained is a K_projective
    replacement of A and of A.unEnd.
  -/
  haveI : ((homotopy_category.quotient _ _).obj fP).is_K_projective,
  { refine ⟨_⟩,
    intros Y hY f,
    convert homotopy_category.eq_of_homotopy _ _
      (projective.null_homotopic_of_projective_to_acyclic f.out N hproj hN' hY.1),
    { simp }, },
  /-
  * Use Ext_iso to calculate both Ext(A,B) and Ext(A.unEnd, B.unEnd) with this replacement.
  -/
end
-/

open_locale zero_object

def single_unEnd (X : endomorphisms 𝓐) : ((single _ 0).obj X).unEnd ≅ (single _ 0).obj X.X :=
{ hom := quot.mk _
  { f := λ i, show (ite (i = 0) X 0).X ⟶ ite (i = 0) X.X 0,
    from if hi : i = 0 then eq_to_hom (by { simp only [if_pos hi] })
      else 0,
    comm' := begin
      rintros i j _,
      change _ ≫ 0 = 0 ≫ _, simp, end },
  inv := quot.mk _ {
    f := λ i, show ite (i = 0) X.X 0 ⟶ (ite (i = 0) X 0).X,
    from if hi : i = 0 then eq_to_hom (by { simp only [if_pos hi] })
      else 0,
    comm' := begin
      rintros i j (rfl : _ = _),
      change _ ≫ 0 = 0 ≫ _, simp, end },
  hom_inv_id' := begin
    change quot.mk _ (_ ≫ _) = quot.mk _ _,
    apply congr_arg,
    ext i,
    simp only [homological_complex.comp_f, homological_complex.id_f],
    split_ifs,
    { simp },
    { rw [comp_zero, eq_comm, ← limits.is_zero.iff_id_eq_zero],
      change is_zero (ite (i = 0) X 0).X,
      rw if_neg h,
      apply is_zero_X,
      apply is_zero_zero,
    },
  end,
  inv_hom_id' := begin
    change quot.mk _ (_ ≫ _) = quot.mk _ _,
    apply congr_arg,
    ext i,
    simp only [homological_complex.comp_f, homological_complex.id_f],
    split_ifs,
    { simp },
    { rw [comp_zero, eq_comm, ← limits.is_zero.iff_id_eq_zero],
      change is_zero (ite (i = 0) X.X 0),
      rw if_neg h,
      apply is_zero_zero, },
  end }

lemma single_unEnd_e (X : endomorphisms 𝓐) :
  (single_unEnd X).hom ≫ (single _ 0).map X.e = ((single _ 0).obj X).e ≫ (single_unEnd X).hom :=
begin
  change quot.mk _ (_ ≫ _) = quot.mk _ _,
  apply congr_arg,
  ext i,
  change dite _ _ _ ≫ dite _ _ _ = _ ≫ dite _ _ _,
  split_ifs,
  { subst h,
    rw [eq_to_hom_trans_assoc, ← category.assoc],
    congr',
    simp,
    refl, },
  { simp, },
end

lemma single_e (X : endomorphisms 𝓐) :
  (single_unEnd X).hom ≫ (single _ 0).map X.e ≫ (single_unEnd X).inv = ((single _ 0).obj X).e :=
by rw [← category.assoc, iso.comp_inv_eq, single_unEnd_e]

open category_theory.preadditive

def embed_single (X : 𝓐) :
  (homological_complex.embed complex_shape.embedding.nat_down_int_up).obj
    ((homological_complex.single 𝓐 (complex_shape.down ℕ) 0).obj X) ≅
  (homological_complex.single 𝓐 (complex_shape.up ℤ) 0).obj X :=
homological_complex.hom.iso_of_components (by rintro ((_|i)|i); exact iso.refl _)
begin
  rintro (i|i) j (rfl : _ = _),
  { apply is_zero.eq_of_tgt, exact is_zero_zero _ },
  { apply is_zero.eq_of_src, exact is_zero_zero _ },
end

def to_bounded_homotopy_category_single (X : 𝓐) :
  chain_complex.to_bounded_homotopy_category.obj ((homological_complex.single _ _ 0).obj X) ≅
  (single _ 0).obj X :=
bounded_homotopy_category.mk_iso $ (homotopy_category.quotient _ _).map_iso $
embed_single X

lemma to_bounded_homotopy_category_single_naturality (X : 𝓐) (f : X ⟶ X) :
  (to_bounded_homotopy_category_single X).op.hom ≫
  (chain_complex.to_bounded_homotopy_category.map
       ((homological_complex.single 𝓐 (complex_shape.down ℕ) 0).map f)).op ≫
    (to_bounded_homotopy_category_single X).op.inv = ((single _ 0).map f).op :=
begin
  dsimp only [iso.op], simp only [← op_comp], congr' 1,
  dsimp only [to_bounded_homotopy_category_single, chain_complex.to_bounded_homotopy_category,
    bounded_homotopy_category.mk_iso, functor.comp_map, functor.map_iso, single,
    homotopy_category.single],
  erw [← functor.map_comp, ← functor.map_comp], congr' 1,
  ext ((_|i)|i),
  { dsimp,
    erw [category.comp_id, category.id_comp],
    convert rfl, },
  { apply is_zero.eq_of_src, apply is_zero_zero },
  { apply is_zero.eq_of_src, apply is_zero_zero },
end

def to_bounded_homotopy_category_mk_end_single (X : 𝓐) (f : X ⟶ X) :
  chain_complex.to_bounded_homotopy_category.obj
    (((homological_complex.single 𝓐 _ 0).obj X).mk_end
       ((homological_complex.single 𝓐 _ 0).map f)) ≅
  (single (endomorphisms 𝓐) 0).obj (⟨X,f⟩) :=
begin
  refine _ ≪≫ to_bounded_homotopy_category_single _,
  apply functor.map_iso,
  refine homological_complex.hom.iso_of_components _ _,
  { rintro (_|i); refine endomorphisms.mk_iso _ _,
    { exact iso.refl _ },
    { dsimp [homological_complex.mk_end],
      simp only [category.id_comp, category.comp_id, if_pos rfl], refl, },
    { apply (is_zero_zero _).iso, apply is_zero_X, apply is_zero_zero },
    { apply (is_zero_zero _).eq_of_src }, },
  { rintro _ i (rfl : _ = _), apply is_zero.eq_of_src, rw is_zero_iff_id_eq_zero, ext, }
end
.

attribute [reassoc] nat_trans.comp_app

lemma Ext'_is_zero_iff (X Y : 𝓐) (f : X ⟶ X) (g : Y ⟶ Y) :
  (∀ i, is_zero (((Ext' i).obj (op $ endomorphisms.mk X f)).obj $ endomorphisms.mk Y g)) ↔
  (∀ i, is_iso $ ((Ext' i).map f.op).app _ - ((Ext' i).obj _).map g) :=
begin
  convert (Ext_is_zero_iff ((homological_complex.single _ _ 0).obj X) Y (functor.map _ f) g)
    using 1,
  { apply propext, apply forall_congr, intro i,
    apply iso.is_zero_iff, dsimp only [Ext', functor.comp_obj, functor.flip_obj_obj],
    apply iso.app, apply functor.map_iso, dsimp only [functor.op_obj], apply iso.op,
    apply to_bounded_homotopy_category_mk_end_single },
  { apply propext, apply forall_congr, intro i,
    let e := ((Ext i).map_iso (to_bounded_homotopy_category_single X).op).app ((single _ 0).obj Y),
    rw [← is_iso.comp_left_iff e.hom, ← is_iso.comp_right_iff _ e.inv],
    simp only [comp_sub, sub_comp, iso.app_hom, iso.app_inv, category.assoc,
      functor.map_iso_hom, functor.map_iso_inv, ← nat_trans.comp_app, ← functor.map_comp,
      to_bounded_homotopy_category_single_naturality],
    clear e,
    dsimp only [Ext', functor.comp_obj, functor.comp_map],
    congr' 3,
    rw [nat_trans.naturality, ← nat_trans.comp_app_assoc, ← functor.map_comp, iso.hom_inv_id,
      functor.map_id, nat_trans.id_app, category.id_comp],
    refl },
end

end endomorphisms

end category_theory
