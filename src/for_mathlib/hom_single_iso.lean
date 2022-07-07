import for_mathlib.derived.K_projective
import for_mathlib.homological_complex_op
import for_mathlib.homology_iso_Ab

noncomputable theory

universes v u

open category_theory category_theory.limits category_theory.preadditive

variables {C : Type u} {ι : Type*} [category.{v} C] [abelian C] {c : complex_shape ι}

def homotopy_category.quotient_map_hom (A B : homological_complex C c) :
  (A ⟶ B) →+ ((homotopy_category.quotient C c).obj A ⟶ (homotopy_category.quotient C c).obj B) :=
add_monoid_hom.mk' (λ f, (homotopy_category.quotient C c).map f) $ λ f g, rfl

lemma quot.mk_surjective {X : Type*} (r : X → X → Prop) :
  function.surjective (quot.mk r) :=
λ x, quot.induction_on x $ λ x, ⟨x, rfl⟩

noncomputable
def homotopy.to_single [decidable_eq ι] [decidable_rel c.rel] {X : homological_complex C c} {B : C}
  {i j : ι} (r : c.rel i j)
  (f g : X ⟶ (homological_complex.single C c i).obj B) (h : X.X j ⟶ B)
  (H : f.f i = X.d i j ≫ h ≫ eq_to_hom (if_pos rfl).symm + g.f i) :
  homotopy f g :=
{ hom := λ i₁ i₂, if r' : c.rel i₂ i₁ then if e : i₂ = i then
    (X.X_eq_to_iso (c.next_eq (e ▸ r' : c.rel i i₁) r)).hom ≫ h ≫ eq_to_hom (if_pos e).symm
    else 0 else 0,
  zero' := λ _ _ e, dif_neg e,
  comm := λ k, begin
    dsimp,
    by_cases k = i,
    swap, { apply is_zero.eq_of_tgt, dsimp, rw if_neg h, exact is_zero_zero _ },
    subst h,
    rw [d_next_eq _ r, dif_pos r, dif_pos rfl, H, X.X_eq_to_iso_refl, category.id_comp],
    nth_rewrite_lhs 0 ← add_monoid.add_zero (X.d k j ≫ h ≫ eq_to_hom _),
    congr,
    delta prev_d,
    rcases c.prev k with (_|⟨i, _⟩); dsimp,
    { refl },
    { rw comp_zero, refl }
  end }

lemma homotopic_to_single_iff [decidable_eq ι] {X : homological_complex C c}
  {B : C} {i j : ι} (r : c.rel i j)
  (f g : X ⟶ (homological_complex.single C c i).obj B) :
  homotopic _ _ f g ↔
    ∃ (h : X.X j ⟶ B), f.f i = X.d i j ≫ h ≫ eq_to_hom (if_pos rfl).symm + g.f i :=
begin
  haveI : decidable_rel c.rel := λ _ _, classical.dec _,
  refine ⟨_, λ ⟨h, H⟩, ⟨homotopy.to_single r f g h H⟩⟩,
  rintro ⟨h⟩,
  use h.hom j i ≫ eq_to_hom (if_pos rfl),
  rw [category.assoc, eq_to_hom_trans, eq_to_hom_refl, category.comp_id, ← add_zero (_ ≫ _)],
  have := h.comm i,
  rw [d_next_eq _ r] at this,
  convert this,
  delta prev_d,
  rcases c.prev i with (_|⟨j, _⟩); dsimp; simp
end

instance : decidable_rel (complex_shape.up ℤ).rel :=
λ i j, show decidable (i + 1 = j), by apply_instance

@[simps] noncomputable
def homological_complex.hom_single_iso
  (P : cochain_complex C ℤ) (B : C) (i : ℤ) :
  (P ⟶ (homological_complex.single C (complex_shape.up ℤ) i).obj B) ≃+
    (add_monoid_hom.ker ((((preadditive_yoneda.obj B).map_homological_complex
      (complex_shape.up ℤ).symm).obj P.op).d i (i - 1))) :=
{ to_fun := λ f, begin
    refine ⟨f.f i ≫ eq_to_hom (if_pos rfl), _⟩,
    change P.d (i - 1) i ≫ f.f i ≫ eq_to_hom _ = 0,
    rw ← f.comm_assoc,
    dsimp,
    rw [zero_comp, comp_zero],
  end,
  inv_fun := λ f, begin
    refine ⟨λ j, if e : j = i then
      (P.X_eq_to_iso $ e).hom ≫ f.1 ≫ eq_to_hom (if_pos e).symm else 0, _⟩,
    rintros j k (rfl : j + 1 = k),
    dsimp,
    rw comp_zero,
    split_ifs,
    { have := eq_sub_iff_add_eq.mpr h, subst this,
      rw [P.X_d_eq_to_iso_assoc, ← category.assoc, ← subtype.val_eq_coe,
        show P.d (i - 1) i ≫ f.1 = 0, from f.2, zero_comp] },
    { exact comp_zero.symm }
  end,
  left_inv := begin
    intro f,
    ext j,
    dsimp,
    split_ifs,
    { subst h, simp },
    { apply is_zero.eq_of_tgt, rw if_neg h, exact is_zero_zero _ }
  end,
  right_inv := λ f, by { ext, dsimp, simp },
  map_add' := λ f g, subtype.ext (preadditive.add_comp _ _ _ _ _ _) }

namespace bounded_homotopy_category

namespace hom_single_iso_setup

def hom_complex
  (P : bounded_homotopy_category C) (B : C) (i : ℤ) :=
(((preadditive_yoneda.obj B).map_homological_complex _).obj P.val.as.op)

def map_hom_complex
  {P₁ P₂ : bounded_homotopy_category C} (f : P₁ ⟶ P₂) (B : C) (i : ℤ) :
  hom_complex P₂ B i ⟶ hom_complex P₁ B i :=
(((preadditive_yoneda.obj B).map_homological_complex _).map
  (homological_complex.op_functor.map f.out.op))

def aux₁
  (P : bounded_homotopy_category C) (B : C) (i : ℤ) :
  homology
    ((hom_complex P B i).d (i+1) i)
    ((hom_complex P B i).d i (i-1))
    ((hom_complex P B i).d_comp_d _ _ _) ≅
  (hom_complex P B i).homology i :=
(homology_iso' (hom_complex P B i) (i+1) i (i-1) (by simp) (by simp)).symm

def map_homology
  {P₁ P₂ : bounded_homotopy_category C} (f : P₁ ⟶ P₂) (B : C) (i : ℤ) :
  homology ((hom_complex P₂ B i).d (i + 1) i) ((hom_complex P₂ B i).d i (i - 1))
    ((hom_complex _ B i).d_comp_d _ _ _) ⟶
  homology ((hom_complex P₁ B i).d (i + 1) i) ((hom_complex P₁ B i).d i (i - 1))
    ((hom_complex _ B i).d_comp_d _ _ _) :=
homology.map _ _
(arrow.hom_mk $ (map_hom_complex f B i).comm _ _)
(arrow.hom_mk $ (map_hom_complex f B i).comm _ _)
rfl

lemma aux₁_naturality
  (P₁ P₂ : bounded_homotopy_category C) (f : P₁ ⟶ P₂) (B : C) (i : ℤ) :
  (aux₁ P₂ B i).hom ≫ (homology_functor _ _ _).map (map_hom_complex f B i) =
  (map_homology f _ _) ≫ (aux₁ P₁ B i).hom :=
begin
  dsimp only [map_homology, aux₁, homology_iso', iso.symm_hom, homology.map_iso,
    homology_functor_map],
  rw homology.map_eq_desc'_lift_left,
  rw homology.map_eq_lift_desc'_left,
  rw homology.map_eq_desc'_lift_left,
  rw homology.map_eq_lift_desc'_left,
  apply homology.hom_from_ext, apply homology.hom_to_ext,
  simp only [homology.π'_desc', category.assoc, homology.π'_desc'_assoc,
    homology.lift_ι, homology.lift_ι_assoc],
  let t := _, change t ≫ _ = _,
  have ht : t = kernel.lift _ (kernel.ι _) _ ≫ homology.π' _ _ _,
  rotate 2,
  { rw homological_complex.d_from_eq,
    rw [kernel.condition_assoc, zero_comp],
    simp, },
  { apply homology.hom_to_ext,
    simp, dsimp, simp },
  rw ht, clear ht, clear t,
  simp only [kernel.lift_ι_assoc, category.assoc, arrow.hom_mk_left, arrow.iso_mk_inv_left,
    iso.refl_inv, homological_complex.hom.sq_from_left, homology.π'_desc'],
  let t := _, change _ = _ ≫ t,
  have ht : t = homology.ι _ _ _ ≫ cokernel.desc _ (cokernel.π _) _,
  rotate 2,
  { have := (hom_complex P₁ B i).d_to_eq (by simp : (complex_shape.up ℤ).symm.rel (i+1) i),
    rw ← iso.inv_comp_eq at this,
    rw [← this, category.assoc, cokernel.condition, comp_zero] },
  { apply homology.hom_from_ext,
    simp, dsimp, simp },
  rw ht, clear ht, clear t,
  simp only [category.assoc, cokernel.π_desc, homology.lift_ι_assoc],
end

def aux₂
  (P : bounded_homotopy_category C) (B : C) (i : ℤ) :
  homology
    ((hom_complex P B i).d (i+1) i)
    ((hom_complex P B i).d i (i-1))
    (homological_complex.d_comp_d _ _ _ _) ≅
  AddCommGroup.homology ((hom_complex P B i).d (i+1) i) ((hom_complex P B i).d i (i-1)) :=
(AddCommGroup.homology_iso _ _ _)

def ker_hom
  {P₁ P₂ : bounded_homotopy_category C} (f : P₁ ⟶ P₂) (B : C) (i : ℤ) :
  ((hom_complex P₂ B i).d i (i - 1)).ker →+
  ((hom_complex P₁ B i).d i (i - 1)).ker :=
{ to_fun := λ x, ⟨(map_hom_complex f B i).f _ ↑x, begin
    change _ = _,
    have : _ = _ := x.2,
    dsimp [hom_complex, map_hom_complex] at *,
    rw [← category.assoc, ← f.out.comm, category.assoc, this, comp_zero],
  end⟩,
  map_zero' := by { ext, simp },
  map_add' := begin
    intros x y, ext, dsimp [map_hom_complex], simp,
  end }

def map_explicit_homology
  {P₁ P₂ : bounded_homotopy_category C} (f : P₁ ⟶ P₂) (B : C) (i : ℤ) :
  AddCommGroup.homology ((hom_complex P₂ B i).d (i+1) i) ((hom_complex P₂ B i).d i (i-1)) ⟶
  AddCommGroup.homology ((hom_complex P₁ B i).d (i+1) i) ((hom_complex P₁ B i).d i (i-1)) :=
quotient_add_group.lift _
(add_monoid_hom.comp (quotient_add_group.mk' _) $ ker_hom f _ _)
begin
  rintros ⟨x,(hx : _ = _)⟩ hh,
  dsimp [ker_hom, map_hom_complex],
  rw quotient_add_group.eq_zero_iff,
  rw add_subgroup.mem_comap at *, dsimp at *,
  change ∃ e, _,
  obtain ⟨e,he⟩ := hh,
  dsimp [hom_complex] at *,
  use f.out.f _ ≫ e,
  rw [← category.assoc, ← f.out.comm, category.assoc, he],
end

--TODO: This relates the above construction to AddcommGroup.homology_map
-- the above def has more convenient defeq properties for some of the proofs below, but
-- the `AddCommGroup.homology_map` is better suited for `aux₂_naturality`.
lemma map_explicit_homology_eq
  {P₁ P₂ : bounded_homotopy_category C} (f : P₁ ⟶ P₂) (B : C) (i : ℤ) :
  map_explicit_homology f B i =
  AddCommGroup.homology_map
    ((hom_complex P₂ B i).d_comp_d _ _ _)
    ((hom_complex P₁ B i).d_comp_d _ _ _)
    (commsq.of_eq $ ((map_hom_complex f B i).comm (i+1) i).symm)
    (commsq.of_eq $ ((map_hom_complex f B i).comm i (i-1)).symm) :=
begin
  ext ⟨t⟩,
  symmetry, apply AddCommGroup.homology_map_apply_mk,
end

lemma aux₂_naturality
  (P₁ P₂ : bounded_homotopy_category C) (f : P₁ ⟶ P₂) (B : C) (i : ℤ) :
  (aux₂ P₂ B i).hom ≫ map_explicit_homology f _ _ =
  map_homology f _ _ ≫ (aux₂ P₁ B i).hom :=
begin
  rw map_explicit_homology_eq,
  dsimp [aux₂],
  dsimp [AddCommGroup.homology_iso, AddCommGroup.homology_map, map_homology],
  generalize_proofs _ _ w _ w',
  apply (homology.has _ _ w).ext_π,
  apply (AddCommGroup.has_homology _ _ w').ext_ι,
  rw has_homology.homology_map_eq,
  simp only [has_homology.π_map, category.assoc, has_homology.π_map_assoc,
    has_homology.map_ι, has_homology.map_ι_assoc],
  let t := _, change t ≫ _ = _,
  have ht : t = kernel.lift _ (kernel.ι _) _ ≫ (AddCommGroup.has_homology _ _ w).π,
  rotate 2,
  { apply kernel.condition },
  { apply (AddCommGroup.has_homology _ _ w).ext_ι,
    simp [has_homology.π_ι] },
  rw ht, clear ht, clear t,
  let t := _, change _ = _ ≫ t,
  have ht : t = (homology.has _ _ w').ι ≫ cokernel.desc _ (cokernel.π _) _,
  rotate 2,
  { apply cokernel.condition },
  { apply (homology.has _ _ w').ext_π,
    rw [← category.assoc, has_homology.π_ι],
    simp },
  rw ht, clear ht, clear t,
  simp,
end

lemma aux₂_naturality_inv
  (P₁ P₂ : bounded_homotopy_category C) (f : P₁ ⟶ P₂) (B : C) (i : ℤ) :
  map_explicit_homology f _ _ ≫ (aux₂ P₁ B i).inv =
  (aux₂ P₂ B i).inv ≫  map_homology f _ _ :=
by rw [iso.comp_inv_eq, category.assoc, iso.eq_inv_comp, aux₂_naturality]

def aux₃
  (P : bounded_homotopy_category C) (B : C) (i : ℤ) :
  (P ⟶ (single C i).obj B) ≃+
  AddCommGroup.homology ((hom_complex P B i).d (i+1) i) ((hom_complex P B i).d i (i-1)) :=
begin
  refine add_equiv.surjective_congr (homological_complex.hom_single_iso P.val.as B i)
    (homotopy_category.quotient_map_hom _ _)
    (quotient_add_group.mk' _) (quot.mk_surjective _) (quot.mk_surjective _) _,
  ext f,
  dsimp,
  simp only [homotopy_category.quotient_map_hom, quotient_add_group.ker_mk,
    add_equiv.coe_to_add_monoid_hom, add_monoid_hom.mem_ker, add_subgroup.mem_comap,
    add_subgroup.coe_subtype, add_monoid_hom.mk'_apply, add_subgroup.coe_mk,
    add_equiv.coe_mk, add_monoid_hom.mem_range],
  rw ← (homotopy_category.quotient _ _).map_zero,
  any_goals { apply_instance },
  erw quotient.functor_map_eq_iff,
  rw homotopic_to_single_iff (show (complex_shape.up ℤ).rel i (i+1), from rfl),
  apply exists_congr,
  intro g,
  simp only [add_zero, quiver.hom.unop_op, linear_map.to_add_monoid_hom_coe,
    preadditive_yoneda_obj_map_apply, homological_complex.zero_f_apply,
    homological_complex.hom_single_iso_apply_coe],
  rw [← is_iso.comp_inv_eq, eq_comm],
  split,
  { intro h,
    rw [h, is_iso.comp_inv_eq, category.assoc, category.assoc, eq_to_hom_trans,
      eq_to_hom_refl, category.comp_id],
    refl },
  { intro h,
    rw [h, is_iso.eq_comp_inv, category.assoc, category.assoc, eq_to_hom_trans,
      eq_to_hom_refl, category.comp_id],
    refl }
end

lemma aux₃_apply
  (P : bounded_homotopy_category C) (B : C) (i : ℤ)
  (f : P ⟶ (single C i).obj B) :
  aux₃ P B i f = quotient_add_group.mk ⟨f.out.f i ≫ eq_to_hom (if_pos rfl), begin
    change _ = _, dsimp [hom_complex],
    rw [← category.assoc, ← f.out.comm, category.assoc],
    convert zero_comp,
    apply is_zero.eq_of_tgt, convert is_zero_zero _,
    dsimp [single], rw if_neg, simp,
  end⟩ := rfl

lemma aux₃_naturality
  (P₁ P₂ : bounded_homotopy_category C) (f : P₁ ⟶ P₂) (B : C) (i : ℤ) :
  (map_explicit_homology f B i).comp (aux₃ P₂ B i).to_add_monoid_hom =
  add_monoid_hom.comp (aux₃ P₁ B i).to_add_monoid_hom ((preadditive_yoneda.obj _).map f.op) :=
begin
  ext ⟨x⟩,
  dsimp, simp_rw aux₃_apply,
  dsimp [map_explicit_homology, ker_hom, map_hom_complex],
  rw ← sub_eq_zero,
  erw ← (quotient_add_group.mk' _).map_sub,
  erw quotient_add_group.eq_zero_iff,
  rw [add_subgroup.mem_comap],
  dsimp,
  -- now we need to use a homotopy...
  simp_rw [← category.assoc, ← homological_complex.comp_f],
  let t := _, let s := _, change homological_complex.hom.f t i ≫ _ -
    homological_complex.hom.f s i ≫ _ ∈ _,
  let hh : homotopy t s := begin
    apply homotopy_category.homotopy_of_eq,
    simpa,
  end,
  let e := hh.hom (i+1) i,
  change ∃ e, _,
  dsimp [hom_complex],
  use e ≫ eq_to_hom (if_pos rfl),
  rw [← preadditive.sub_comp _ _ (eq_to_hom _), ← category.assoc,
    ← homological_complex.comp_f], congr' 1,
  erw hh.comm i,
  simp only [homological_complex.cochain_complex_d_next,
    homological_complex.cochain_complex_prev_d, add_sub_cancel,
    self_eq_add_right],
  exact comp_zero,
end

lemma comp_add_equiv_iso_AddcommGroup_iso_eq_comp
  (X X' B : AddCommGroup.{u}) (e' : X' ≃+ B) (f : X ⟶ X') :
  f ≫ (add_equiv_iso_AddCommGroup_iso.hom e').hom =
  e'.to_add_monoid_hom.comp f := rfl

def hom_mk {A B : Type u} [add_comm_group A] [add_comm_group B] (f : A →+ B) :
  (AddCommGroup.of A) ⟶ (AddCommGroup.of B) := f

end hom_single_iso_setup

open hom_single_iso_setup

noncomputable
def hom_single_iso
  (P : bounded_homotopy_category C) (B : C) (i : ℤ) :
  AddCommGroup.of (P ⟶ (bounded_homotopy_category.single C i).obj B) ≅
  (((preadditive_yoneda.obj B).map_homological_complex _).obj P.val.as.op).homology i :=
begin
  refine _ ≪≫ aux₁ P B i,
  refine add_equiv_iso_AddCommGroup_iso.hom _ ≪≫ (aux₂ P B i).symm,
  exact aux₃ P B i,
end

.

open opposite

variables {X Y Z : cochain_complex C ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)

def of' (X : cochain_complex C ℤ)
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj X)] :
  bounded_homotopy_category C :=
of $ (homotopy_category.quotient _ _).obj X

def of_hom (f : X ⟶ Y)
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj X)]
  [homotopy_category.is_bounded_above ((homotopy_category.quotient _ _).obj Y)] :
  of' X ⟶ of' Y :=
(homotopy_category.quotient _ _).map f

instance val_as_bdd_above (P : bounded_homotopy_category C) :
  ((homotopy_category.quotient C (complex_shape.up ℤ)).obj P.val.as).is_bounded_above :=
by { rcases P with ⟨P, ⟨a, ha⟩⟩, use a, intros i hi, exact ha i hi }

lemma hom_single_iso_naturality
  (P₁ P₂ : bounded_homotopy_category C) (B : C) (i : ℤ)
  (f : P₁ ⟶ P₂) :
  (preadditive_yoneda.obj _).map f.op ≫ (hom_single_iso P₁ B i).hom =
  (hom_single_iso P₂ B i).hom ≫
  (((preadditive_yoneda.obj B).right_op.map_homological_complex _ ⋙
      homological_complex.unop_functor.right_op ⋙
      (_root_.homology_functor _ _ _).op).map f.out).unop :=
begin
  dsimp only [hom_single_iso, iso.trans_hom, iso.symm_hom, functor.comp_map, functor.op_map,
    functor.right_op_map, quiver.hom.unop_op],
  simp_rw [← category.assoc, comp_add_equiv_iso_AddcommGroup_iso_eq_comp],
  rw ← aux₃_naturality,
  rw [category.assoc],

  let t := hom_mk (aux₃ P₂ B i).to_add_monoid_hom,
  change (t ≫ (map_explicit_homology f B i)) ≫ _ ≫ _ = _,
  slice_lhs 2 3
  { rw aux₂_naturality_inv },
  simp_rw category.assoc,
  rw ← aux₁_naturality,
  refl,
end

lemma hom_single_iso_naturality'
  (P₁ P₂ : bounded_homotopy_category C) (B : C) (i : ℤ)
  (f : P₁.val.as ⟶ P₂.val.as) :
  (preadditive_yoneda.obj ((single C i).obj B)).map (of_hom f).op ≫ (hom_single_iso P₁ B i).hom =
  (hom_single_iso P₂ B i).hom ≫
  (((preadditive_yoneda.obj B).right_op.map_homological_complex _ ⋙
      homological_complex.unop_functor.right_op ⋙
      (_root_.homology_functor _ _ _).op).map f).unop :=
begin
  erw hom_single_iso_naturality P₁ P₂ B i (of_hom f),
  refine congr_arg2 _ rfl _,
  apply homology_map_eq_of_homotopy,
  let h := (preadditive_yoneda.obj B).right_op.map_homotopy (homotopy_category.homotopy_out_map f),
  refine ⟨λ i j, (h.hom j i).unop, _, _⟩,
  { intros i j hij, rw [h.zero, unop_zero], exact hij },
  { intros i,
    conv_rhs { congr, rw add_comm, },
    convert congr_arg quiver.hom.unop (h.comm i),
    { dsimp [op_equiv, prev_d, d_next],
      have hi := (complex_shape.up ℤ).next_eq_some (show i+1=i+1, by refl),
      have hi' := (complex_shape.up ℤ).symm.prev_eq_some (show i+1=i+1, by refl),
      simpa only [hi, hi'], },
    { dsimp [op_equiv, prev_d, d_next],
      have hi := (complex_shape.up ℤ).prev_eq_some (show i-1+1=i, by linarith),
      have hi' := (complex_shape.up ℤ).symm.next_eq_some (show i-1+1=i, by linarith),
      simpa only [hi, hi'], }, },
end

lemma hom_single_iso_naturality_snd_var
  (P : bounded_homotopy_category C) {B₁ B₂ : C} (i : ℤ)
  (f : B₁ ⟶ B₂) (x : P ⟶ (single C i).obj B₁) :
  ((homology_functor _ _ i).map
    ((nat_trans.map_homological_complex (preadditive_yoneda.map f) _).app P.val.as.op))
      ((hom_single_iso P B₁ i).hom x) = ((hom_single_iso P B₂ i).hom (x ≫ (single C i).map f)) :=
begin
  sorry,
end

end bounded_homotopy_category
