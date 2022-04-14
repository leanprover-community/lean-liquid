import condensed.is_proetale_sheaf
import condensed.adjunctions
import category_theory.limits.filtered_colimit_commutes_finite_limit

open category_theory
open category_theory.limits

universe u
variables
  {J : Type (u+1)} [small_category J] [is_filtered J]
  {C : Type (u+2)}
  [category.{u+1} C]
  [concrete_category.{u+1} C]
  [has_limits C]
  [has_colimits_of_shape J C]
  [preserves_colimits_of_shape J (forget C)]
  [reflects_limits (forget C)]
  [preserves_limits (forget C)]
  (F : J ⥤ Condensed.{u} C)

open opposite

namespace is_sheaf_colimit_presheaf_aux

namespace empty

variables (G : J ⥤ Profinite.{u}ᵒᵖ ⥤ C)

noncomputable
def comparison_component (j : J) :
  (G.obj j).obj (op Profinite.empty) ⟶ ⊤_ _ := terminal.from _

variables [∀ j, is_iso (comparison_component G j)]

noncomputable
def first_iso : (colimit G).obj (op Profinite.empty) ≅
  colimit (limit (functor.empty _ ⋙ G.flip)) :=
let e₁ := is_colimit_of_preserves ((evaluation _ _).obj (op Profinite.empty))
  (colimit.is_colimit G),
    e₂ := e₁.cocone_point_unique_up_to_iso (colimit.is_colimit _),
    e₃ : G ⋙ (evaluation Profiniteᵒᵖ C).obj (op Profinite.empty) ≅
      limit (functor.empty Profiniteᵒᵖ ⋙ G.flip) :=
      nat_iso.of_components
      (λ j,
        let e₄ := is_limit_of_preserves ((evaluation _ _).obj j)
          (limit.is_limit (functor.empty _ ⋙ G.flip)),
            e₅ := (limit.is_limit _).cone_point_unique_up_to_iso e₄,
            e₆ : functor.empty C ≅
              (functor.empty Profiniteᵒᵖ ⋙ G.flip) ⋙ (evaluation J C).obj j :=
              nat_iso.of_components (λ i, i.elim) (λ i, i.elim) in
        as_iso (comparison_component G j) ≪≫
          has_limit.iso_of_nat_iso e₆ ≪≫ e₅)
      begin
        intros X Y f, dsimp [comparison_component],
        apply (is_limit_of_preserves ((evaluation J C).obj Y)
          (limit.is_limit (functor.empty Profiniteᵒᵖ ⋙ G.flip))).hom_ext,
        intros j, cases j,
      end in
e₂ ≪≫ has_colimit.iso_of_nat_iso e₃

noncomputable
def second_iso : colimit (limit (functor.empty _ ⋙ G.flip)) ≅
  limit (colimit (functor.empty _ ⋙ G.flip).flip) :=
  colimit_limit_iso _

noncomputable
def third_iso : limit (colimit (functor.empty _ ⋙ G.flip).flip) ≅ ⊤_ _ :=
has_limit.iso_of_nat_iso $ nat_iso.of_components (λ i, i.elim) (λ i, i.elim)

noncomputable
def comparison : (colimit G).obj (op Profinite.empty) ⟶ ⊤_ _ := terminal.from _

theorem is_iso_comparison : is_iso (comparison G) :=
begin
  suffices : comparison G = (first_iso G).hom ≫ (second_iso G).hom ≫ (third_iso G).hom,
  { rw this, apply_instance },
  simp,
end

end empty

namespace prod

variables (X Y : Profinite.{u}) (G : J ⥤ Profinite.{u}ᵒᵖ ⥤ C)

noncomputable
def comparison_component (j : J) :
  (G.obj j).obj (op $ Profinite.sum X Y) ⟶ prod ((G.obj j).obj (op X)) ((G.obj j).obj (op Y)) :=
prod.lift ((G.obj j).map (Profinite.sum.inl _ _).op) ((G.obj j).map (Profinite.sum.inr _ _).op)

variables [∀ j, is_iso (comparison_component X Y G j)]

noncomputable
def first_iso_aux_aux (j) :
  (G ⋙ (evaluation Profiniteᵒᵖ C).obj (op (X.sum Y))).obj j ≅
  (G.flip.obj (op X) ⨯ G.flip.obj (op Y)).obj j :=
let e₄ : pair ((G.obj j).obj (op X)) ((G.obj j).obj (op Y)) ≅
  pair (G.flip.obj (op X)) (G.flip.obj (op Y)) ⋙ (evaluation J C).obj j :=
  nat_iso.of_components
  (λ p, match p with
    | walking_pair.left := iso.refl _
    | walking_pair.right := iso.refl _
    end) begin
      rintros (_|_) (_|_) (_|_), refl, refl,
    end in
as_iso (comparison_component X Y G j) ≪≫
  has_limit.iso_of_nat_iso e₄ ≪≫
  (limit.is_limit _).cone_point_unique_up_to_iso
    (is_limit_of_preserves ((evaluation _ _).obj j) (limit.is_limit _))

noncomputable
def first_iso_aux : G ⋙ (evaluation Profiniteᵒᵖ C).obj (op (X.sum Y)) ≅
  G.flip.obj (op X) ⨯ G.flip.obj (op Y) :=
nat_iso.of_components (λ j, first_iso_aux_aux X Y G j)
begin
  intros i j f, dsimp [comparison_component, first_iso_aux_aux],
  apply
    (is_limit_of_preserves ((evaluation J C).obj j)
      (limit.is_limit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))))).hom_ext,
  rintros (_|_),
  { dsimp [is_limit.cone_point_unique_up_to_iso],
    have h1 :=
      (is_limit_of_preserves ((evaluation J C).obj j)
        (limit.is_limit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))))).fac
          (limit.cone _) walking_pair.left,
    have h2 :=
      (is_limit_of_preserves ((evaluation J C).obj i)
        (limit.is_limit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))))).fac
          (limit.cone _) walking_pair.left,
    dsimp at h1 h2, simp [h1, reassoc_of h2],
    dsimp [first_iso_aux_aux._match_1], simp },
  { dsimp [is_limit.cone_point_unique_up_to_iso],
    have h1 :=
      (is_limit_of_preserves ((evaluation J C).obj j)
        (limit.is_limit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))))).fac
          (limit.cone _) walking_pair.right,
    have h2 :=
      (is_limit_of_preserves ((evaluation J C).obj i)
        (limit.is_limit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))))).fac
          (limit.cone _) walking_pair.right,
    dsimp at h1 h2, simp [h1, reassoc_of h2],
    dsimp [first_iso_aux_aux._match_1], simp },
end

noncomputable
def first_iso : (colimit G).obj (op $ Profinite.sum X Y) ≅
  colimit (prod (G.flip.obj (op X)) (G.flip.obj (op Y))) :=
let e₁ := is_colimit_of_preserves ((evaluation _ _).obj (op $ Profinite.sum X Y))
  (colimit.is_colimit G),
    e₂ := e₁.cocone_point_unique_up_to_iso (colimit.is_colimit _) in
e₂ ≪≫ has_colimit.iso_of_nat_iso (first_iso_aux X Y G)

noncomputable
def second_iso : colimit (prod (G.flip.obj (op X)) (G.flip.obj (op Y))) ≅
  limit (colimit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))).flip) :=
colimit_limit_iso _

@[simps] noncomputable
def third_iso_aux_left :
  (colimit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))).flip).obj walking_pair.left ≅
  (colimit G).obj (op X) :=
let e₁ :=
  is_colimit_of_preserves ((evaluation _ _).obj walking_pair.left)
    (colimit.is_colimit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))).flip),
    e₂ :=
  is_colimit_of_preserves ((evaluation _ _).obj (op X))
    (colimit.is_colimit G) in
e₁.cocone_point_unique_up_to_iso e₂

@[simps] noncomputable
def third_iso_aux_right :
  (colimit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))).flip).obj walking_pair.right ≅
  (colimit G).obj (op Y) :=
let e₁ :=
  is_colimit_of_preserves ((evaluation _ _).obj walking_pair.right)
    (colimit.is_colimit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))).flip),
    e₂ :=
  is_colimit_of_preserves ((evaluation _ _).obj (op Y))
    (colimit.is_colimit G) in
e₁.cocone_point_unique_up_to_iso e₂

/--/
noncomputable
def third_iso_aux : cone (pair (op X) (op Y) ⋙ colimit G) :=
{ X := limit (colimit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))).flip),
  π :=
  { app := λ p,
    match p with
    | walking_pair.left := limit.π _ walking_pair.left ≫ (third_iso_aux_left X Y G).hom
    | walking_pair.right := limit.π _ walking_pair.right ≫ (third_iso_aux_right X Y G).hom
    end,
    naturality' := sorry } }

noncomputable
def third_iso_aux' : cone (colimit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))).flip) :=
{ X := limit (pair (op X) (op Y) ⋙ colimit G),
  π :=
  { app := λ p,
    match p with
    | walking_pair.left := limit.π _ walking_pair.left ≫ (third_iso_aux_left X Y G).inv
    | walking_pair.right := limit.π _ walking_pair.right ≫ (third_iso_aux_right X Y G).inv
    end,
    naturality' := sorry } }
-/

@[simps] noncomputable
def third_iso_aux : cone (colimit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))).flip) :=
{ X := prod ((colimit G).obj (op X)) ((colimit G).obj (op Y)),
  π :=
  { app := λ p,
    match p with
    | walking_pair.left := limits.prod.fst ≫ (third_iso_aux_left _ _ _).inv
    | walking_pair.right := limits.prod.snd ≫ (third_iso_aux_right _ _ _).inv
    end,
    naturality' := begin
      rintros (_|_) (_|_) (_|_),
      { dsimp [third_iso_aux._match_1], simp },
      { dsimp [third_iso_aux._match_1], simp },
    end } }

noncomputable
def third_iso :
  limit (colimit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))).flip)
    ≅ prod ((colimit G).obj (op X)) ((colimit G).obj (op Y)) :=
{ hom := prod.lift
    (limit.π _ walking_pair.left ≫ (third_iso_aux_left _ _ _).hom)
    (limit.π _ walking_pair.right ≫ (third_iso_aux_right _ _ _).hom),
  inv := limit.lift _ (third_iso_aux _ _ _),
  hom_inv_id' := begin
    ext (_|_),
    { simp, dsimp [third_iso_aux, third_iso_aux._match_1], simp },
    { simp, dsimp [third_iso_aux, third_iso_aux._match_1], simp },
  end,
  inv_hom_id' := begin
    ext,
    { simp, dsimp [third_iso_aux], simp },
    { simp, dsimp [third_iso_aux], simp },
  end }

/-
noncomputable
def fourth_iso_aux : cone (pair (op X) (op Y) ⋙ colimit G) :=
{ X := prod ((colimit G).obj (op X)) ((colimit G).obj (op Y)),
  π :=
  { app := λ p,
    match p with
    | walking_pair.left := limits.prod.fst
    | walking_pair.right := limits.prod.snd
    end,
    naturality' := sorry } }

noncomputable
def fourth_iso : limit (pair (op X) (op Y) ⋙ colimit G) ≅
  prod ((colimit G).obj (op X)) ((colimit G).obj (op Y)) :=
{ hom := prod.lift (limit.π _ walking_pair.left) (limit.π _ walking_pair.right),
  inv := limit.lift _ (fourth_iso_aux _ _ _),
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }
-/

noncomputable
def comparison : (colimit G).obj (op $ Profinite.sum X Y) ⟶
  prod ((colimit G).obj (op X)) ((colimit G).obj (op Y)) :=
prod.lift
  ((colimit G).map (Profinite.sum.inl _ _).op)
  ((colimit G).map (Profinite.sum.inr _ _).op)

lemma is_iso_comparison : is_iso (comparison X Y G) :=
begin
  suffices : (comparison X Y G) =
    (first_iso X Y G).hom ≫ (second_iso X Y G).hom ≫ (third_iso X Y G).hom,
  { rw this, apply_instance },
  sorry
end

end prod

namespace eq

variables {X Y : Profinite.{u}} (f : X ⟶ Y) (G : J ⥤ Profinite.{u}ᵒᵖ ⥤ C)

noncomputable
def comparison_component (j : J) :
  (G.obj j).obj (op $ Y) ⟶
  equalizer
    ((G.obj j).map (Profinite.pullback.fst f f).op)
    ((G.obj j).map (Profinite.pullback.snd f f).op) :=
equalizer.lift ((G.obj j).map f.op)
begin
  simp_rw [← (G.obj j).map_comp, ← op_comp, Profinite.pullback.condition],
end

variables [∀ j, is_iso (comparison_component f G j)]

noncomputable
def first_iso : (colimit G).obj (op $ Y) ≅
  colimit (equalizer
    (G.flip.map (Profinite.pullback.fst f f).op)
    (G.flip.map (Profinite.pullback.snd f f).op)) :=
let e₁ := is_colimit_of_preserves
  ((evaluation _ _).obj (op $ Y)) (colimit.is_colimit G),
    e₂ := e₁.cocone_point_unique_up_to_iso (colimit.is_colimit _),
    e₃ : G ⋙ (evaluation Profiniteᵒᵖ C).obj (op Y) ≅
      equalizer (G.flip.map (Profinite.pullback.fst f f).op)
        (G.flip.map (Profinite.pullback.snd f f).op) :=
      nat_iso.of_components (λ j,
        let e₄ : parallel_pair ((G.obj j).map (Profinite.pullback.fst f f).op)
                  ((G.obj j).map (Profinite.pullback.snd f f).op) ≅
                 parallel_pair (G.flip.map (Profinite.pullback.fst f f).op)
                  (G.flip.map (Profinite.pullback.snd f f).op) ⋙
                  (evaluation J C).obj j :=
            nat_iso.of_components (λ p,
              match p with
              | walking_parallel_pair.zero := iso.refl _
              | walking_parallel_pair.one := iso.refl _
              end)
            sorry in
        as_iso (comparison_component f G j)
          ≪≫
          has_limit.iso_of_nat_iso e₄
          ≪≫ (limit.is_limit _).cone_point_unique_up_to_iso
          (is_limit_of_preserves ((evaluation _ _).obj j) (limit.is_limit _)))
      sorry in
e₂ ≪≫ has_colimit.iso_of_nat_iso e₃

noncomputable
def second_iso : colimit (equalizer
    (G.flip.map (Profinite.pullback.fst f f).op)
    (G.flip.map (Profinite.pullback.snd f f).op)) ≅
    limit (colimit (parallel_pair
      (G.flip.map (Profinite.pullback.fst f f).op)
      (G.flip.map (Profinite.pullback.snd f f).op)).flip) :=
colimit_limit_iso _

noncomputable
def third_iso_aux :
  (colimit (parallel_pair (G.flip.map (Profinite.pullback.fst f f).op)
    (G.flip.map (Profinite.pullback.snd f f).op)).flip).obj
    walking_parallel_pair.zero ≅ (colimit G).obj (op X) :=
let e₁ :=
  is_colimit_of_preserves ((evaluation _ _).obj walking_parallel_pair.zero)
    (colimit.is_colimit (parallel_pair (G.flip.map (Profinite.pullback.fst f f).op)
    (G.flip.map (Profinite.pullback.snd f f).op)).flip),
    e₂ := is_colimit_of_preserves ((evaluation _ _).obj (op X)) (colimit.is_colimit G) in
e₁.cocone_point_unique_up_to_iso e₂

noncomputable
def third_iso_aux' : cone (colimit (parallel_pair
      (G.flip.map (Profinite.pullback.fst f f).op)
      (G.flip.map (Profinite.pullback.snd f f).op)).flip) :=
{ X := equalizer
      ((colimit G).map (Profinite.pullback.fst f f).op)
      ((colimit G).map (Profinite.pullback.snd f f).op),
  π :=
  { app := λ p,
    match p with
    | walking_parallel_pair.zero := equalizer.ι _ _ ≫ (third_iso_aux _ _).inv
    | walking_parallel_pair.one := equalizer.ι _ _ ≫ (third_iso_aux f G).inv ≫
        category_theory.functor.map _ walking_parallel_pair_hom.left
    end,
  naturality' := begin
    rintro (_|_) (_|_) ⟨⟩,
    { dsimp, simp only [category.id_comp, category_theory.functor.map_id, category.comp_id], },
    { dsimp [third_iso_aux'._match_1], simp only [category.id_comp, category.assoc], },
    { dsimp [third_iso_aux'._match_1], simp only [category.id_comp, category.assoc], sorry, },
    { dsimp, simp only [category.id_comp, category_theory.functor.map_id, category.comp_id], },
  end } }

noncomputable
def third_iso : limit (colimit (parallel_pair
      (G.flip.map (Profinite.pullback.fst f f).op)
      (G.flip.map (Profinite.pullback.snd f f).op)).flip) ≅
    equalizer
      ((colimit G).map (Profinite.pullback.fst f f).op)
      ((colimit G).map (Profinite.pullback.snd f f).op) :=
{ hom := equalizer.lift
    (limit.π _ walking_parallel_pair.zero ≫ (third_iso_aux f G).hom) sorry,
  inv := limit.lift _ (third_iso_aux' _ _),
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }

noncomputable
def comparison :
  (colimit G).obj (op $ Y) ⟶
  equalizer
    ((colimit G).map (Profinite.pullback.fst f f).op)
    ((colimit G).map (Profinite.pullback.snd f f).op) :=
equalizer.lift ((colimit G).map f.op) sorry

theorem is_iso_comparison : is_iso (comparison f G) :=
begin
  suffices : comparison f G =
    (first_iso f G).hom ≫ (second_iso f G).hom ≫ (third_iso f G).hom,
  { rw this, apply_instance },
  sorry
end

end eq

end is_sheaf_colimit_presheaf_aux
open is_sheaf_colimit_presheaf_aux

/-
variables {K : Type (u+1)} [small_category K] [fin_category K]
  (E : K ⥤ Profinite.{u}ᵒᵖ) [has_limit E] (G : J ⥤ Profinite.{u}ᵒᵖ ⥤ C)
  [∀ j, preserves_limits_of_shape K (G.obj j)]

noncomputable
def comparison_map_component (j : J) : (G.obj j).obj (limit E) ⟶ limit (E ⋙ G.obj j) :=
limit.lift (E ⋙ G.obj j) $ (G.obj j).map_cone (limit.cone E)

noncomputable
def comparison_map : (colimit G).obj (limit E) ⟶ limit (E ⋙ colimit G) :=
limit.lift (E ⋙ colimit G) $ (colimit G).map_cone (limit.cone E)

noncomputable
def first_iso : (colimit G).obj (limit E) ≅ colimit (limit (E ⋙ G.flip)) :=
let e := is_colimit_of_preserves ((evaluation _ _).obj (limit E))
  (colimit.is_colimit G),
  ee := e.cocone_point_unique_up_to_iso (colimit.is_colimit _),
  tt : G ⋙ (evaluation Profiniteᵒᵖ C).obj (limit E) ≅ limit (E ⋙ G.flip) :=
    nat_iso.of_components (λ j, begin
      dsimp,
      refine (is_limit_of_preserves (G.obj j) (limit.is_limit E)).cone_point_unique_up_to_iso
        (limit.is_limit _) ≪≫ _,
      refine _ ≪≫ (limit.is_limit _).cone_point_unique_up_to_iso
        ((is_limit_of_preserves ((evaluation _ _).obj j) (limit.is_limit _))),
      dsimp,
      refine has_limit.iso_of_nat_iso _,
      refine nat_iso.of_components _ _,
      intros k, exact iso.refl _,
      intros k₁ k₂ f, dsimp, simp,
    end) sorry in
ee ≪≫ has_colimit.iso_of_nat_iso tt

noncomputable
def second_iso : colimit (limit (E ⋙ G.flip)) ≅ limit (colimit (E ⋙ G.flip).flip) :=
  colimit_limit_iso _

noncomputable
def third_iso : limit (colimit (E ⋙ G.flip).flip) ≅ limit (E ⋙ colimit G) :=
has_limit.iso_of_nat_iso $
nat_iso.of_components (λ k,
  let ee := (is_colimit_of_preserves ((evaluation _ _).obj k)
    (colimit.is_colimit (E ⋙ G.flip).flip)).cocone_point_unique_up_to_iso
    (colimit.is_colimit _) in
  ee ≪≫
  begin
    dsimp,
    refine _ ≪≫
      (colimit.is_colimit _).cocone_point_unique_up_to_iso
      ((is_colimit_of_preserves ((evaluation _ _).obj (E.obj k)) (colimit.is_colimit _))),
    dsimp,
    refine has_colimit.iso_of_nat_iso _,
    refine nat_iso.of_components _ _,
    intros j, exact iso.refl _,
    intros i j f, dsimp, simp,
  end) sorry

lemma is_iso : is_iso (comparison_map E G) :=
begin
  suffices : comparison_map E G =
    (first_iso E G).hom ≫ (second_iso E G).hom ≫ (third_iso E G).hom,
  { rw this, apply_instance },
  sorry,
end

-- Use the comparison map above
variable (K)
def key : preserves_limits_of_shape K (colimit G) := sorry

end is_sheaf_colimit_presheaf_aux
open is_sheaf_colimit_presheaf_aux

theorem empty_condition_iff_preserves (G : Profiniteᵒᵖ ⥤ C) :
  G.empty_condition' ↔
  nonempty (preserves_limits_of_shape (discrete pempty.{u+1}) G) := sorry

theorem product_condition_iff_preserves (G : Profiniteᵒᵖ ⥤ C) :
  G.product_condition' ↔
  nonempty (preserves_limits_of_shape (discrete walking_pair.{u+1}) G) := sorry

theorem equalizer_condition_iff_preserves (G : Profiniteᵒᵖ ⥤ C) :
  G.equalizer_condition' ↔
  nonempty (preserves_limits_of_shape (walking_parallel_pair.{u+1}) G) := sorry
-/

lemma is_sheaf_colimit_presheaf :
  presheaf.is_sheaf proetale_topology (colimit (F ⋙ Sheaf_to_presheaf _ _)) :=
begin
  --rw is_sheaf_iff_is_sheaf_of_type,
  let G := (colimit (F ⋙ Sheaf_to_presheaf _ _)),
  let Gs := F ⋙ Sheaf_to_presheaf _ _,
  have hGs : ∀ j, presheaf.is_sheaf proetale_topology (Gs.obj j),
  { intros j, exact (F.obj j).2 },
  have hGsempty : ∀ j, (Gs.obj j).empty_condition',
  { intros j, specialize hGs j,
    rw (Gs.obj j).is_proetale_sheaf_tfae.out 0 3 at hGs,
    exact hGs.1 },
  have hGsprod : ∀ j, (Gs.obj j).product_condition',
  { intros j, specialize hGs j,
    rw (Gs.obj j).is_proetale_sheaf_tfae.out 0 3 at hGs,
    exact hGs.2.1 },
  have hGseq : ∀ j, (Gs.obj j).equalizer_condition',
  { intros j, specialize hGs j,
    rw (Gs.obj j).is_proetale_sheaf_tfae.out 0 3 at hGs,
    exact hGs.2.2 },
  rw G.is_proetale_sheaf_tfae.out 0 3,
  refine ⟨_,_,_⟩,
  { apply_with empty.is_iso_comparison { instances := ff },
    exact hGsempty,
    all_goals { apply_instance } },
  { intros X Y,
    apply_with prod.is_iso_comparison { instances := ff },
    intros j, apply hGsprod,
    all_goals { apply_instance } },
  { intros X Y f hf,
    apply_with eq.is_iso_comparison { instances := ff },
    intros j, apply hGseq, assumption' }
end

@[simps]
noncomputable
def filtered_cocone : cocone F :=
{ X := ⟨colimit (F ⋙ Sheaf_to_presheaf _ _), is_sheaf_colimit_presheaf _⟩,
  ι :=
  { app := λ j, Sheaf.hom.mk $ colimit.ι (F ⋙ Sheaf_to_presheaf _ _) j,
    naturality' := begin
      intros i j f,
      ext1, dsimp,
      simpa using colimit.w (F ⋙ Sheaf_to_presheaf _ _) f,
    end } }

noncomputable
def filtered_cocone_is_colimit : is_colimit (filtered_cocone F) :=
{ desc := λ S, Sheaf.hom.mk $ colimit.desc (F ⋙ Sheaf_to_presheaf _ _)
    ((Sheaf_to_presheaf _ _).map_cocone S),
  fac' := begin
    intros S j,
    ext1, dsimp,
    simp,
  end,
  uniq' := begin
    intros S m hm,
    ext1, dsimp,
    apply colimit.hom_ext,
    intros j, specialize hm j, apply_fun (λ e, e.val) at hm,
    dsimp at hm, simpa using hm,
  end }
