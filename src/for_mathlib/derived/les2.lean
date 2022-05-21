import for_mathlib.derived.lemmas
import for_mathlib.derived.les
import for_mathlib.derived.derived_cat

open category_theory
open category_theory.limits
open category_theory.triangulated

universes v u

variables {A : Type u} [category.{v} A] [abelian A]

local notation `𝒦` := homotopy_category A (complex_shape.up ℤ)

namespace homological_complex
variables {X Y Z : cochain_complex A ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)

noncomputable theory

-- The 5-lemma with no instances... I think this is more convenient to apply in practice.
lemma _root_.category_theory.abelian.is_iso_of_is_iso_of_is_iso_of_is_iso_of_is_iso' :
  ∀ {U B C D A' B' C' D' : A} {f : U ⟶ B} {g : B ⟶ C}
  {h : C ⟶ D} {f' : A' ⟶ B'} {g' : B' ⟶ C'} {h' : C' ⟶ D'} {α : U ⟶ A'} {β : B ⟶ B'} {γ : C ⟶ C'}
  {δ : D ⟶ D'},
    α ≫ f' = f ≫ β →
    β ≫ g' = g ≫ γ →
    γ ≫ h' = h ≫ δ →
    ∀ {E E' : A} {i : D ⟶ E} {i' : D' ⟶ E'} {ε : E ⟶ E'},
      δ ≫ i' = i ≫ ε →
      exact f g → exact g h → exact h i →  exact f' g' →
      exact g' h' → exact h' i' → is_iso α →  is_iso β →
      is_iso δ → is_iso ε → is_iso γ :=
begin
  intros U B C D A' B' C' D' f g h f' g' h' α β γ δ w1 w2 w3 E E' i i' ε w4,
  intros hfg hgh hhi hf'g' hg'h' hh'i' hα hβ hδ hε, resetI,
  apply abelian.is_iso_of_is_iso_of_is_iso_of_is_iso_of_is_iso
    w1 w2 w3 w4 hfg hgh hhi hf'g' hg'h' hh'i',
end

namespace is_iso_cone_setup

-- This follows from the fact that homology is a homological functor.
lemma is_zero_homology_cone_id (n : ℤ) :
  is_zero ((cone (𝟙 X)).homology n) :=
begin
  let T : triangle (homotopy_category A (complex_shape.up ℤ)) :=
    (neg₃_functor _).obj (cone.triangleₕ (𝟙 X)),
  have hT : T ∈ dist_triang 𝒦,
  { erw homotopy_category.mem_distinguished_iff_exists_iso_cone,
    refine ⟨_, _, 𝟙 X, ⟨iso.refl _⟩⟩ },
  have E := five_term_exact_seq' (homotopy_category.homology_functor A
    (complex_shape.up ℤ) n) T hT,
  dsimp [T] at E,
  sorry -- use E.
end

def cone_id_to_cone :
  cone (𝟙 X) ⟶ cone f :=
{ f := λ i, biprod.lift biprod.fst (biprod.snd ≫ f.f _),
  comm' := sorry }

-- `0 → C(𝟙 X) → C(f) → Z → 0` is a SES of complexes.
lemma cone_id_to_cone_short_exact (ses : ∀ i : ℤ, short_exact (f.f i) (g.f i))
  (n : ℤ) : short_exact ((cone_id_to_cone f).f n)
  ((cone.π f g (λ i, (ses i).exact.w)).f _) := sorry

/-
Now combine both results above to see that the map
`H^i(C(f)) → H^i(Z)`
is an isomorphism, using the LES for short exact sequences of complexes.
-/

lemma is_iso_homology_map_cone_π (ses : ∀ i : ℤ, short_exact (f.f i) (g.f i))
  (n : ℤ) :
  is_iso ((homology_functor _ _ n).map (cone.π f g (λ i, (ses i).exact.w))) :=
begin
  have E := six_term_exact_seq (cone_id_to_cone f)
    (cone.π f g (λ i, (ses i).exact.w)) (cone_id_to_cone_short_exact _ _ _),
  -- now use E along with `is_zero_homology_cone_id`.
  sorry
end

end is_iso_cone_setup

-- Why is this SO SLOW?!
lemma is_iso_homology_functor_map_aux (n : ℤ) (ses : ∀ i : ℤ, short_exact (f.f i) (g.f i)) :
  (homology_functor A (complex_shape.up ℤ) n).map (cone.π f g (λ i, (ses i).exact.w)) ≫
    δ f g ses n (n + 1) rfl =
  (homotopy_category.homology_functor A (complex_shape.up ℤ) n).map
    ((neg₃_functor (homotopy_category A (complex_shape.up ℤ))).obj
      (cone.triangleₕ f)).mor₃ ≫ ((homology_shift_iso A 1 n).app
    ((neg₃_functor (homotopy_category A (complex_shape.up ℤ))).obj
      (cone.triangleₕ f)).obj₁.as).hom :=
begin
  sorry
end

theorem is_iso_homology_functor_map (n : ℤ) (ses : ∀ (i : ℤ), short_exact (f.f i) (g.f i)) :
  is_iso ((homology_functor _ _ n).map (cone.π f g (λ i, (ses i).exact.w))) :=
begin
  let X' : 𝒦 := (homotopy_category.quotient _ _).obj X,
  let Y' : 𝒦 := (homotopy_category.quotient _ _).obj Y,
  let Z' : 𝒦 := (homotopy_category.quotient _ _).obj Z,
  let f' : X' ⟶ Y' := (homotopy_category.quotient _ _).map f,
  let g' : Y' ⟶ Z' := (homotopy_category.quotient _ _).map g,
  let T : triangle (homotopy_category A (complex_shape.up ℤ)) :=
    (neg₃_functor _).obj (cone.triangleₕ f),
  have hT : T ∈ dist_triang 𝒦,
  { erw homotopy_category.mem_distinguished_iff_exists_iso_cone,
    refine ⟨_, _, f, ⟨iso.refl _⟩⟩ },
  have E1 := five_term_exact_seq' (homotopy_category.homology_functor A (complex_shape.up ℤ) n)
    T hT,
  have E2 := six_term_exact_seq f g ses n (n+1) rfl,
  let EE := homology_shift_iso A 1 n,
  --rw zero_add at EE,
  have key := @_root_.category_theory.abelian.is_iso_of_is_iso_of_is_iso_of_is_iso_of_is_iso' _ _ _
    ((homotopy_category.homology_functor _ _ n).obj T.obj₁)
    ((homotopy_category.homology_functor _ _ n).obj T.obj₂)
    ((homotopy_category.homology_functor _ _ n).obj T.obj₃)
    ((homotopy_category.homology_functor _ _ n).obj (T.obj₁⟦(1 : ℤ)⟧))
    ((homology_functor _ _ n).obj X)
    ((homology_functor _ _ n).obj Y)
    ((homology_functor _ _ n).obj Z)
    ((homology_functor _ _ (n+1)).obj X)
    ((homotopy_category.homology_functor _ _ n).map T.mor₁)
    ((homotopy_category.homology_functor _ _ n).map T.mor₂)
    ((homotopy_category.homology_functor _ _ n).map T.mor₃)
    ((homology_functor _ _ n).map f)
    ((homology_functor _ _ n).map g)
    (δ f g ses n (n+1) rfl)
    (𝟙 _) (𝟙 _)
    ((homology_functor _ _ n).map (cone.π f g _))
    (EE.app _).hom _ _ _
    ((homotopy_category.homology_functor _ _ n).obj (T.obj₂⟦(1 : ℤ)⟧))
    ((homology_functor _ _ (n+1)).obj Y)
    ((homotopy_category.homology_functor A (complex_shape.up ℤ) n).map T.rotate.mor₃)
    ((homology_functor A (complex_shape.up ℤ) (n+1)).map f)
    (-(EE.app _)).hom,
    apply key, any_goals { apply_instance },
  { dsimp [triangle.rotate],
    simp only [functor.map_neg, preadditive.comp_neg, preadditive.neg_comp, neg_neg],
    symmetry,
    apply EE.hom.naturality },
  { exact E1.pair },
  { exact (E1.drop 1).pair },
  { exact (E1.drop 2).pair },
  { exact E2.pair },
  { exact (E2.drop 1).pair },
  { exact (E2.drop 2).pair },
  { simp only [category.id_comp, category.comp_id], refl },
  { rw category.id_comp,
    change _ = (homology_functor _ _ _).map _ ≫ _,
    rw ← functor.map_comp,
    congr' 1, ext i, symmetry, apply biprod.inr_snd_assoc },
  { apply is_iso_homology_functor_map_aux },
end .

instance is_quasi_iso_map_cone_π (ses : ∀ (i : ℤ), short_exact (f.f i) (g.f i)) :
  homotopy_category.is_quasi_iso
    ((homotopy_category.quotient _ _).map (cone.π f g (λ i, (ses i).exact.w))) :=
begin
  constructor, intros i,
  apply is_iso_homology_functor_map,
end

end homological_complex

namespace homotopy_category

variables {X Y Z : cochain_complex A ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)
open homological_complex

def cone := (homotopy_category.quotient _ _).obj (cone f)

def cone.π (w) : cone f ⟶ (homotopy_category.quotient _ _).obj Z :=
(homotopy_category.quotient _ _).map (cone.π f g w)

instance is_quasi_iso_cone_π
  (w : ∀ i, short_exact (f.f i) (g.f i)) : is_quasi_iso (cone.π f g _) :=
homological_complex.is_quasi_iso_map_cone_π _ _ w

end homotopy_category

namespace homological_complex

end homological_complex

namespace bounded_homotopy_category

variables {X Y Z : cochain_complex A ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)
open homological_complex

def cone
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj X)]
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj Y)]
  (f : X ⟶ Y) :
  bounded_homotopy_category A :=
{ val := homotopy_category.cone f,
  bdd := begin
    obtain ⟨a,ha⟩ :=
      homotopy_category.is_bounded_above.cond ((homotopy_category.quotient _ _).obj X),
    obtain ⟨b,hb⟩ :=
      homotopy_category.is_bounded_above.cond ((homotopy_category.quotient _ _).obj Y),
    constructor, use (max a b + 1),
    intros t ht,
    apply is_zero_biprod,
    { apply ha, refine le_trans (le_trans _ ht) _,
      refine le_trans (le_max_left a b) _,
      all_goals { linarith } },
    { apply hb,
      refine le_trans _ ht, refine le_trans (le_max_right a b) _,
      linarith }
  end }

def of' (X : cochain_complex A ℤ)
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj X)] :
  bounded_homotopy_category A :=
of $ (homotopy_category.quotient _ _).obj X

def cone.π
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj X)]
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj Y)]
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj Z)]
  (w) : cone f ⟶ of' Z :=
homotopy_category.cone.π f g w

instance is_quasi_iso_cone_π
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj X)]
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj Y)]
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj Z)]
  (w : ∀ i, short_exact (f.f i) (g.f i)) :
  homotopy_category.is_quasi_iso (cone.π f g _) :=
homological_complex.is_quasi_iso_map_cone_π _ _ w

def of_hom (f : X ⟶ Y)
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj X)]
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj Y)] :
  of' X ⟶ of' Y :=
(homotopy_category.quotient _ _).map f

def cone_triangle
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj X)]
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj Y)] :
  triangle (bounded_homotopy_category A) :=
{ obj₁ := of' X,
  obj₂ := of' Y,
  obj₃ := cone f,
  mor₁ := of_hom f,
  mor₂ := (cone.triangleₕ f).mor₂,
  mor₃ := -(cone.triangleₕ f).mor₃, }

lemma dist_cone_triangle
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj X)]
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj Y)] :
  cone_triangle f ∈ dist_triang (bounded_homotopy_category A) :=
homotopy_category.cone_triangleₕ_mem_distinguished_triangles _ _ f

instance is_iso_Ext_map_cone_π
  (n : ℤ)
  [enough_projectives A]
  (W : bounded_homotopy_category A)
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj X)]
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj Y)]
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj Z)]
  (w : ∀ i, short_exact (f.f i) (g.f i)) :
  is_iso (((Ext n).flip.obj W).right_op.map (cone.π f g (λ i, (w i).exact.w))) :=
begin
  dsimp [functor.right_op],
  apply_with category_theory.is_iso_op { instances := ff },
  apply bounded_homotopy_category.is_iso_Ext_flip_obj_map_of_is_quasi_iso,
end

def connecting_hom'
  (n : ℤ)
  [enough_projectives A]
  (W : bounded_homotopy_category A)
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj X)]
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj Y)]
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj Z)]
  (w : ∀ i, short_exact (f.f i) (g.f i)) :
  ((Ext n).flip.obj W).right_op.obj (of' Z) ⟶
  ((Ext n).flip.obj W).right_op.obj ((of' X)⟦(1 : ℤ)⟧) :=
inv (((Ext n).flip.obj W).right_op.map ((cone.π f g (λ i, (w i).exact.w)))) ≫
((Ext n).flip.obj W).right_op.map (cone_triangle f).mor₃

def Ext_five_term_exact_seq
  (n : ℤ)
  [enough_projectives A]
  (W : bounded_homotopy_category A)
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj X)]
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj Y)]
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj Z)]
  (w : ∀ i, short_exact (f.f i) (g.f i)) :
  let E := ((Ext n).flip.obj W).right_op in
  exact_seq Ab.{v}ᵒᵖ $
    [ E.map (of_hom f)
    , E.map (of_hom g)
    , connecting_hom' f g n W w
    , E.map (-(of_hom f)⟦(1 : ℤ)⟧')] :=
begin
  intros E,
  have hg : of_hom g = (cone_triangle f).mor₂ ≫ (cone.π f g (λ i, (w i).exact.w)),
  { dsimp [of_hom, cone_triangle, cone.π, homotopy_category.cone.π],
    erw [← functor.map_comp], congr' 1,
    ext ii,
    dsimp [cone.in], rw biprod.inr_snd_assoc },
  let e := (E.map ((cone.π f g (λ i, (w i).exact.w)))),
  let ee := as_iso e,
  have firsttwo := homological_functor.cond E (cone_triangle f) (dist_cone_triangle _),
  apply exact_seq.cons,
  { rw [hg, functor.map_comp],
    rw exact_comp_iso,
    apply firsttwo },
  apply exact_seq.cons,
  { have next_two :=
      homological_functor.cond E (cone_triangle f).rotate _,
    dsimp only [connecting_hom'], rw [hg, functor.map_comp],
    change exact (_ ≫ ee.hom) (ee.inv ≫ _),
    rw category_theory.exact_comp_hom_inv_comp_iff,
    exact next_two,
    apply pretriangulated.rot_of_dist_triangle, apply dist_cone_triangle },
  rw ← exact_iff_exact_seq,
  { dsimp only [connecting_hom'],
    rw exact_iso_comp,
    apply homological_functor.cond E (cone_triangle f).rotate.rotate,
    apply pretriangulated.rot_of_dist_triangle,
    apply pretriangulated.rot_of_dist_triangle,
    apply dist_cone_triangle },
end
.


def shift_iso [enough_projectives A]
  (n : ℤ) (X : cochain_complex A ℤ) (Y : bounded_homotopy_category A)
  [((homotopy_category.quotient A (complex_shape.up ℤ)).obj X).is_bounded_above] :
  (((Ext (n+1)).flip.obj Y)).obj (opposite.op $ (of' X)⟦(1:ℤ)⟧) ≅
  (((Ext n).flip.obj Y)).obj (opposite.op $ (of' X)) :=
begin
  let e := Ext_iso n (of' X).replace (of' X) Y (of' X).π,
  let e' := Ext_iso (n+1) ((of' X).replace⟦1⟧) ((of' X)⟦1⟧) Y ((of' X).π⟦(1:ℤ)⟧'),
  refine (e' ≪≫ _ ≪≫ e.symm),
  clear e e',
  refine add_equiv.to_AddCommGroup_iso _,
  let se := shift_equiv (bounded_homotopy_category A) (1:ℤ),
  sorry
end

lemma shift_iso_conj
  (n : ℤ)
  [enough_projectives A]
  (W : bounded_homotopy_category A)
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj X)]
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj Y)] :
  (shift_iso _ _ _).inv ≫ (((Ext (n+1)).flip.obj W).right_op.map (-(of_hom f)⟦(1 : ℤ)⟧')).unop
    ≫ (shift_iso _ _ _).hom =
  ((Ext n).flip.obj W).map (of_hom f).op :=
begin
  -- this should be true up to a minus sign
  sorry
end

def Ext_δ
  (n : ℤ)
  [enough_projectives A]
  (W : bounded_homotopy_category A)
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj X)]
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj Y)]
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj Z)]
  (w : ∀ i, short_exact (f.f i) (g.f i)) :
  ((Ext n).flip.obj W).obj (opposite.op $ of' X) ⟶
  ((Ext (n+1)).flip.obj W).obj (opposite.op $ of' Z) :=
(shift_iso n X W).inv ≫ (connecting_hom' f g (n+1) W w).unop

def Ext_five_term_exact_seq'
  (n : ℤ)
  [enough_projectives A]
  (W : bounded_homotopy_category A)
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj X)]
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj Y)]
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj Z)]
  (w : ∀ i, short_exact (f.f i) (g.f i)) :
  let E := λ n, ((Ext n).flip.obj W) in
  exact_seq Ab.{v} $
    [ (E n).map (of_hom g).op
    , (E n).map (of_hom f).op
    , Ext_δ f g n W w
    , (E (n+1)).map (of_hom g).op ] :=
begin
  refine (Ext_five_term_exact_seq f g n W w).pair.unop.cons _,
  refine exact.cons _ (exact.exact_seq _),
  { rw [Ext_δ, functor.right_op_map, quiver.hom.unop_op, ← shift_iso_conj f n W,
      exact_iso_comp, exact_comp_hom_inv_comp_iff],
    exact (Ext_five_term_exact_seq f g (n+1) W w).unop.pair, },
  { rw [Ext_δ, exact_iso_comp],
    exact ((Ext_five_term_exact_seq f g (n+1) W w).drop 1).pair.unop, }
end

end bounded_homotopy_category

namespace bounded_derived_category

variables [enough_projectives A]
variables {X Y Z : bounded_derived_category A} (f : X ⟶ Y) (g : Y ⟶ Z)
open homological_complex

def cone (f : X ⟶ Y) : bounded_derived_category A :=
(localization_functor _).obj $
{ val := homotopy_category.cone f.val.out,
  bdd := begin
    obtain ⟨a,ha⟩ := homotopy_category.is_bounded_above.cond X.val.val,
    obtain ⟨b,hb⟩ := homotopy_category.is_bounded_above.cond Y.val.val,
    constructor, use (max a b + 1),
    intros t ht,
    apply is_zero_biprod,
    { apply ha, refine le_trans (le_trans _ ht) _,
      refine le_trans (le_max_left a b) _,
      all_goals { linarith } },
    { apply hb,
      refine le_trans _ ht, refine le_trans (le_max_right a b) _,
      linarith }
  end }

-- UGH
end bounded_derived_category
