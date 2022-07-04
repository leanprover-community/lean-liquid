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

instance {P Q : bounded_homotopy_category (endomorphisms 𝓐)} (f : P ⟶ Q)
  [homotopy_category.is_quasi_iso f] :
homotopy_category.is_quasi_iso (((endomorphisms.forget _).map_bounded_homotopy_category).map f) :=
-- This presumably isn't so bad
sorry

instance forget_preserves_K_projective {P : bounded_homotopy_category (endomorphisms 𝓐)}
  [P.val.is_K_projective] :
((endomorphisms.forget 𝓐).map_bounded_homotopy_category.obj P).val.is_K_projective :=
-- Adam says that he knows a messy proof of this but it might need AB4 (i.e. this sorry
-- might no even be true in this generality)
sorry

def forget_mk_end (X : chain_complex 𝓐 ℕ) (f : X ⟶ X) :
  (endomorphisms.forget 𝓐).map_bounded_homotopy_category.obj
    (chain_complex.to_bounded_homotopy_category.obj (homological_complex.mk_end X f)) ≅
  chain_complex.to_bounded_homotopy_category.obj X :=
bounded_homotopy_category.mk_iso $ (homotopy_category.quotient _ _).map_iso $
homological_complex.hom.iso_of_components
(λ m,
match m with
| int.of_nat 0 := iso.refl _
| int.of_nat (i+1) := is_zero.iso (functor.map_is_zero _ $ is_zero_zero _) (is_zero_zero _)
| -[1+i] := iso.refl _
end)
begin
  rintros i j (rfl : _ = _),
  -- I have no idea how hard this sorry is. Probably just a grotty case bash.
  sorry,
end


/-

Mathematical summary of the `Ext_is_zero_iff` `sorry` according to kmb's
possibly flawed understanding:

The lemma will follow from the following things:

1) If X is a complex in the bounded homotopy category
and Y is an object, thought of as a `single`
complex, then Extⁱ(X,Y) is the homology of the complex
(Cᵢ) whose i'th term is Hom(Pⁱ,Y), where P is a projective
replacement of X. This applies to both the category 𝓐
and to the endomorphism category. The reason is
that Extⁱ(X,Y)=Hom(P,Y⟦i⟧).

2) For a cleverly chosen choice of Pⁱ (see `exists_K_projective_endomorphism_replacement`)
we have a short exact sequence of complexes
0 -> Hom_{endos}(Pⁱ,Y) -> Hom(Pⁱ,Y) -> Hom(Pⁱ,Y)->0
where the surjection is e(P) - e(Y), with e the endomorphism.
This can be checked to be surjective via an explicit construction;
the trick is that Pⁱ is going to be `free Q` for some object `Q : 𝓐`

-/

-- We no longer need this lemma, which is true but whose proof will probably be a
-- huge hassle. Thanks Jo\"el Riou!
-- lemma exists_K_projective_endomorphism_replacement
--   (X : bounded_homotopy_category (endomorphisms 𝓐)) :
-- ∃ (P : bounded_homotopy_category (endomorphisms 𝓐))
--   (f : P ⟶ X),
--   homotopy_category.is_K_projective P.val ∧
--   homotopy_category.is_quasi_iso f
--   ∧ (∀ j, ∃ (Q : 𝓐) (i: P.val.as.X j ≅ free Q), projective Q)
-- --  ∧ ∀ k, projective (P.val.as.X k) -- should follow
-- --  ∧ ∀ k, projective (P.val.as.X k).X -- should follow
-- := sorry

/-

Next: make the complexes Hom_T(P^*,Y) and Hom(P^*,Y)
Next: make the SES

-/
/-

Idea : We need a short exact sequence of complexes as above, and then
the below follows from the associated long exact sequence
of cohomology.

* SES
* six_term_exact_seq

-/

variables (Y : 𝓐) (g : Y ⟶ Y) (P : bounded_homotopy_category (endomorphisms 𝓐))

def C₁ (Y : endomorphisms 𝓐) (P : bounded_homotopy_category (endomorphisms 𝓐)) :=
((preadditive_yoneda.obj Y).map_homological_complex _).obj P.val.as.op

def C₂  (Y : 𝓐) (P : bounded_homotopy_category (endomorphisms 𝓐)) :=
((preadditive_yoneda.obj Y).map_homological_complex _).obj P.unEnd.val.as.op

def map₁ : C₁ ⟨Y,g⟩ P ⟶ C₂ Y P :=
{ f := λ i,
  { to_fun := endomorphisms.hom.f,
    map_zero' := rfl,
    map_add' := λ _ _, rfl },
  comm' := λ i j h, rfl }

open category_theory.preadditive

def map₂ : C₂ Y P ⟶ C₂ Y P :=
{ f := λ i, add_monoid_hom.mk' (λ ψ, (P.val.as.X i).e ≫ ψ - ψ ≫ g) begin
      intros a b,
      simp only [comp_add, add_comp, sub_eq_add_neg, neg_add, add_assoc],
      congr' 1, apply add_left_comm,
    end,
  comm' := λ i j, begin
    rintro (rfl : _ = _),
    dsimp only [C₂],
    ext1 x,
    dsimp,
    simp only [comp_apply, add_monoid_hom.mk'_apply, linear_map.to_add_monoid_hom_coe,
      preadditive_yoneda_obj_map_apply, comp_sub, ← category.assoc],
    congr' 2,
    have := (endomorphisms.hom.comm (P.val.as.d j (j+1))).symm,
    exact this,
  end }

lemma map₁_mono (n : ℤ) : mono ((map₁ Y g P).f n) :=
begin
  -- this should be easy
  sorry
end

lemma map₂_epi {n : ℤ} (h : projective (P.val.as.X n)) : epi ((map₂ Y g P).f n) :=
begin
  -- this is Joel Riou's argument, reduce to `free` and do an explicit calculation
  sorry
end

lemma map₁₂_exact {n : ℤ} (h : projective (P.val.as.X n)) :
  exact ((map₁ Y g P).f n) ((map₂ Y g P).f n) :=
begin
  -- this should be easy
  sorry
end

lemma map₁₂_short_exact {n : ℤ} (h : projective (P.val.as.X n)) :
  short_exact ((map₁ Y g P).f n) ((map₂ Y g P).f n) :=
{ mono := map₁_mono _ _ _ _,
  epi := map₂_epi _ _ _ h,
  exact := map₁₂_exact _ _ _ h }

lemma homology_is_zero_iff_is_iso (h : ∀ n, projective (P.val.as.X n)) :
  (∀ i, is_zero ((homology_functor _ _ i).obj (C₁ ⟨Y, g⟩ P))) ↔
  (∀ j, is_iso ((homology_functor _ _ j).map (map₂ Y g P))) :=
begin
  -- a similar result is proved as `is_zero_iff_epi_and_is_iso` in `derived/les_facts`
  -- This shouldn't be too bad.
  sorry
end

lemma Ext_is_zero_iff (X : chain_complex 𝓐 ℕ) (Y : 𝓐)
  (f : X ⟶ X) (g : Y ⟶ Y) :
  (∀ i, is_zero (((Ext i).obj (op $ chain_complex.to_bounded_homotopy_category.obj
    (X.mk_end f))).obj $ (single _ 0).obj ⟨Y, g⟩)) ↔
  (∀ i, is_iso $ ((Ext i).map (chain_complex.to_bounded_homotopy_category.map f).op).app _ -
                 ((Ext i).obj (op _)).map ((single _ 0).map g)) :=
begin
  obtain ⟨P, _inst, fP, h1, h2⟩ := exists_K_projective_replacement
    (chain_complex.to_bounded_homotopy_category.obj (X.mk_end f)),
  resetI,
  have foo : ∀ (h : ℤ → Prop), (∀ i, h i) ↔ (∀ i, h (-i)),
  { intro h, split,
    { intros h1 i, apply h1 (-i) },
    { intros h1 i, specialize h1 (-i), rwa neg_neg at h1, } },
  convert homology_is_zero_iff_is_iso Y g P h2,
  { apply propext,
    rw foo,
    apply forall_congr,
    intro i,
    have := Ext_iso (-i) P
      (chain_complex.to_bounded_homotopy_category.obj (homological_complex.mk_end X f))
      ((single (endomorphisms 𝓐) 0).obj {X := Y, e := g}) fP,
    rw iso.is_zero_iff this, clear this,
    delta C₁,
    apply iso.is_zero_iff,
    have := hom_single_iso P ⟨Y, g⟩ i,
    refine iso.trans _ this, clear this,
    have := (shift_single_iso 0 (-i) : single (endomorphisms 𝓐) 0 ⋙ _ ≅ _),
    change (preadditive_coyoneda.obj (op P)).obj _ ≅
      (preadditive_coyoneda.obj (op P)).obj _,
    apply (preadditive_coyoneda.obj (op P)).map_iso,
    convert iso.app this ⟨Y, g⟩, -- I ♥ you Lean, this just worked first time
    ring, },
  { apply propext,
    rw foo,
    apply forall_congr,
    intro i,
    let fP' := ((endomorphisms.forget _).map_bounded_homotopy_category).map fP ≫ (forget_mk_end X f).hom,
    let j : (((Ext (-i)).obj (op (chain_complex.to_bounded_homotopy_category.obj X))).obj ((single 𝓐 0).obj Y))
    ≅ ((homology_functor AddCommGroup (complex_shape.up ℤ).symm i).obj (C₂ Y P)),
    { -- need that post-composing with an iso sends quasi-isos to quasi-isos! More precisely:
      -- Above I sorried that if fP is a quasi-iso then so is
      -- ((endomorphisms.forget _).map_bounded_homotopy_category).map fP,
      -- however unfortunately we now need to post-compose with something
      -- which is close to, but not equal to, 𝟙.
      -- This should hopefully be straightforward
      haveI : homotopy_category.is_quasi_iso fP' := sorry,
      refine iso.trans (Ext_iso (-i) _ _ ((single 𝓐 0).obj Y) fP') _,
--      delta C₂,
      refine iso.trans _ (hom_single_iso ((endomorphisms.forget 𝓐).map_bounded_homotopy_category.obj P) Y i),
      have := (shift_single_iso 0 (-i) : single 𝓐 0 ⋙ _ ≅ _),
      -- guide Lean the right way
      change (preadditive_coyoneda.obj (op ((endomorphisms.forget 𝓐).map_bounded_homotopy_category.obj P))).obj _ ≅ _,
      apply (preadditive_coyoneda.obj _).map_iso,
      convert iso.app this _, -- I just used `convert` to define data but I think it's OK because
      -- it's only a proof which needs converting.
      ring, },
    -- Goal is `is_iso f : A ⟶ A` iff `is_iso f' : A' ⟶ A'` and we have an
    -- iso `j : A ⟶ A'` so it suffices to prove that the square
    -- (with `j` on two sides) commutes.
    suffices : j.hom ≫ ((homology_functor AddCommGroup (complex_shape.up ℤ).symm i).map (map₂ Y g P))
      = (((Ext (-i)).map (chain_complex.to_bounded_homotopy_category.map f).op).app ((single 𝓐 0).obj Y) -
      ((Ext (-i)).obj (op (chain_complex.to_bounded_homotopy_category.obj X))).map ((single 𝓐 0).map g)) ≫ j.hom,
    { rw [← is_iso_iff_is_iso_comp_left j.hom, this, is_iso_iff_is_iso_comp_right], },
    delta map₂,
    --simp only [j],
    -- this looks horrible
    -- It's of the form j ≫ (a - b) = (c - d) ≫ j
    -- and in fact j ≫ a = c ≫ j and j ≫ b = d ≫ j are both true
    -- so perhaps the next goal is reducing to that.
    -- I don't know how horrible this will be. Maybe `j` will be
    -- horrible to work with.
    sorry },
end

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
    simp_rw [category.comp_id, category.id_comp],
    erw [category.comp_id, category.id_comp],
    refl, },
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
