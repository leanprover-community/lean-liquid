import for_mathlib.derived.K_projective
import for_mathlib.complex_extend
import for_mathlib.projectives
import for_mathlib.two_step_resolution
import data.zmod.basic

.

universes v u

open category_theory homotopy_category

variables {C : Type u} {ι : Type*} [category.{v} C] [abelian C] {c : complex_shape ι}

open_locale zero_object

instance projective_zero : projective (0 : C) :=
{ factors := λ E X f e he, ⟨0, by ext⟩ }

lemma is_zero_homology_of_exact {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hfg : exact f g) :
  is_zero (homology f g hfg.w) :=
begin
  rw preadditive.exact_iff_homology_zero at hfg,
  rcases hfg with ⟨w, ⟨e⟩⟩,
  exact is_zero_of_iso_of_zero (is_zero_zero _) e.symm,
end

lemma category_theory.is_zero.exact {X Y Z : C} (hY : is_zero Y)
  (f : X ⟶ Y) (g : Y ⟶ Z) : exact f g :=
by simp only [abelian.exact_iff, hY.eq_zero_of_tgt f, hY.eq_zero_of_tgt (limits.kernel.ι g),
    limits.zero_comp, eq_self_iff_true, and_true]

lemma category_theory.is_zero.homology_is_zero {X Y Z : C} (hY : is_zero Y)
  (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) :
  is_zero (homology f g w) :=
is_zero_homology_of_exact f g $ hY.exact f g

variables [enough_projectives C]

lemma category_theory.is_zero.is_iso {X Y : C} (hX : is_zero X) (hY : is_zero Y) (f : X ⟶ Y) :
  is_iso f :=
{ out := ⟨0, hX.eq_of_src _ _, hY.eq_of_tgt _ _⟩ }

lemma category_theory.is_iso_of_nat_iso {C D : Type*} [category C] [category D]
  {F G : C ⥤ D} (α : F ≅ G)
  {X Y : C} (f : X ⟶ Y) (h : is_iso (F.map f)) :
  is_iso (G.map f) :=
begin
  rw ← nat_iso.naturality_1 α f,
  apply_instance,
end

lemma category_theory.nat_iso.is_iso_iff {C D : Type*} [category C] [category D]
  {F G : C ⥤ D} (α : F ≅ G)
  {X Y : C} (f : X ⟶ Y) :
  is_iso (F.map f) ↔ is_iso (G.map f) :=
⟨category_theory.is_iso_of_nat_iso α _, category_theory.is_iso_of_nat_iso α.symm _⟩

open category_theory

@[simps obj obj_val map]
noncomputable def chain_complex.to_bounded_homotopy_category :
  chain_complex C ℕ ⥤ bounded_homotopy_category C :=
{ obj := λ P,
  { val := (homological_complex.embed (complex_shape.embedding.nat_down_int_up) ⋙
      homotopy_category.quotient C _).obj P,
    bdd := begin
      refine ⟨⟨1, _⟩⟩,
      rintro ((_|i)|i) h,
      { exfalso, revert h, dec_trivial },
      { exact is_zero_zero _ },
      { exfalso, revert h, dec_trivial }
    end },
  map := λ P Q f, (homological_complex.embed (complex_shape.embedding.nat_down_int_up) ⋙
      homotopy_category.quotient C _).map f,
  map_id' := λ P, (homological_complex.embed (complex_shape.embedding.nat_down_int_up) ⋙
      homotopy_category.quotient C _).map_id P,
  map_comp' := λ P Q R f g, (homological_complex.embed (complex_shape.embedding.nat_down_int_up) ⋙
      homotopy_category.quotient C _).map_comp f g }

lemma chain_complex.to_bounded_homotopy_category.is_K_projective (P : chain_complex C ℕ)
  (A : C) (π : P ⟶ (chain_complex.single₀ C).obj A)
  (hP : P.is_projective_resolution A π) :
  is_K_projective (chain_complex.to_bounded_homotopy_category.obj P).val :=
begin
  constructor,
  introsI Y hY f,
  rw [← quotient_map_out f],
  apply eq_of_homotopy,
  refine projective.null_homotopic_of_projective_to_acyclic _ 1 _ _ hY.cond,
  { rintro ((_|i)|i),
    { exact hP.projective 0 },
    { exact projective_zero, },
    { exact hP.projective _ }, },
  { rintro ((_|i)|i),
    { intro h, exfalso, revert h, dec_trivial },
    { intro h, exact is_zero_zero _ },
    { intro h, exfalso, revert h, dec_trivial } },
end
.

noncomputable
def homological_complex.homology_functor_single [decidable_eq ι] (i : ι) :
  homological_complex.single C c i ⋙ homology_functor C c i ≅ 𝟭 C :=
begin
  refine nat_iso.of_components _ _,
  { intro X,
    refine homology.congr _ _ _ _ ≪≫ homology_zero_zero ≪≫ _,
    { delta homological_complex.d_to,
      rcases c.prev i with (_|⟨_, _⟩),
      { dsimp, rw if_pos rfl },
      { dsimp, rw limits.comp_zero } },
    { delta homological_complex.d_from,
      rcases c.next i with (_|⟨_, _⟩),
      { dsimp, rw if_pos rfl },
      { dsimp, rw limits.zero_comp } },
    { exact eq_to_iso (if_pos rfl) } },
  { intros X Y f,
    apply homology.ext,
    dsimp,
    simpa only [category.comp_id, homological_complex.hom.sq_from_left, eq_to_hom_refl,
      homological_complex.single_obj_X_self_hom, homology.map_desc_assoc, eq_to_hom_trans,
      homological_complex.single_obj_X_self_inv, homological_complex.single_map_f_self,
      category.assoc, limits.kernel_subobject_map_arrow, homology.π_desc_assoc] }
end

instance {X Y Z : C} (f: X ⟶ Y) : is_iso (homology.ι f (0 : Y ⟶ Z) limits.comp_zero) :=
begin
  suffices : limits.cokernel.desc f 0 limits.comp_zero = 0,
  { exact @@is_iso.comp_is_iso _ _ (show _, by convert limits.kernel.ι_zero_is_iso) },
  ext,
  simp,
end

lemma homology.desc_zero_is_iso_of_exact_of_epi {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  [h : exact f g] [epi g] : is_iso (homology.desc' f (0 : Y ⟶ W) limits.comp_zero
    (limits.kernel_zero_iso_source.hom ≫ g) (by simp)) :=
begin
  convert_to is_iso (homology.ι _ _ _ ≫
    (limits.colimit.iso_colimit_cocone ⟨_, abelian.is_colimit_of_exact_of_epi f g h⟩).hom),
  { ext, simp },
  { apply_instance }
end

lemma chain_complex.is_projective_resolution.is_quasi_iso_embed {P : chain_complex C ℕ}
  {A : C} {π : P ⟶ (chain_complex.single₀ C).obj A}
  (hP : P.is_projective_resolution A π) :
  is_quasi_iso ((homological_complex.embed (complex_shape.embedding.nat_down_int_up) ⋙
       homotopy_category.quotient C _).map π) :=
begin
  constructor,
  intro i,
  rw [← functor.comp_map, category_theory.nat_iso.is_iso_iff
    (functor.associator _ _ _ ≪≫ iso_whisker_left _ (homology_factors _ _ _))],
  rcases i with ((_|i)|i),
  { apply_with is_iso.of_is_iso_comp_right { instances := ff },
    show is_iso (functor.map_iso _ (chain_complex.single₀_comp_embed_iso_single.app A) ≪≫
        ((homological_complex.homology_functor_single (0 : ℤ)).app A : _)).hom, by apply_instance,
    apply_with is_iso.of_is_iso_comp_left { instances := ff },
    swap 2, convert @@homology.desc_zero_is_iso_of_exact_of_epi _ _ _ _ _ hP.exact₀ hP.epi using 1,
    swap 4,
    { refine (homology.map_iso _ _ (arrow.iso_mk _ _ _)
        (arrow.iso_mk _ (by exact iso.refl _) _) rfl).hom,
      { exact ((homological_complex.embed.obj complex_shape.embedding.nat_down_int_up P).X_prev_iso
          (show (complex_shape.up ℤ).rel (-[1+0]) 0, from neg_add_self 1)).symm },
      { exact iso.refl _ },
      { dsimp,
        rw [eq_comm, iso.eq_inv_comp, category.comp_id, eq_comm],
        apply homological_complex.d_to_eq },
      { dsimp,
        rw [category.comp_id, category.id_comp],
        rw homological_complex.d_from_eq _ (show (complex_shape.up ℤ).rel 0 1, from rfl),
        exact limits.zero_comp } },
    { ext,
      dsimp [homology.map_iso, homological_complex.homology_functor_single],
      rw [← cancel_epi (limits.kernel_subobject_iso _).hom, homology.π'_eq_π_assoc],
      simp only [homology.desc'_π', category.comp_id, homological_complex.hom.sq_from_left,
        limits.kernel_subobject_arrow_assoc, homology.π_desc, homology.map_desc,
        limits.kernel_subobject_map_arrow_assoc, arrow.iso_mk_hom_left,
        limits.kernel_subobject_map_arrow],
      dsimp [chain_complex.single₀_comp_embed_iso_single,
        chain_complex.single₀_comp_embed_iso_single_component],
      simpa,
      apply_instance },
    { apply_instance } },
  { refine is_zero.is_iso _ _ _; refine is_zero_homology_of_exact _ _ _, },
  { refine is_zero.is_iso _ _ _,
    { refine is_zero_of_iso_of_zero _ (homology_iso _ (-[1+i.succ] : ℤ) _ (-i : ℤ) _ _).symm,
      rotate,
      { dsimp, refl, },
      { dsimp, simp only [int.neg_succ_of_nat_eq', sub_add_cancel], },
      refine is_zero_homology_of_exact _ _ _,
      cases i; exact (hP.exact _), },
    { refine is_zero_of_iso_of_zero _ (homology_iso _ (-[1+i.succ] : ℤ) _ (-i : ℤ) _ _).symm,
      rotate,
      { dsimp, refl, },
      { dsimp, simp only [int.neg_succ_of_nat_eq', sub_add_cancel], },
      refine is_zero_homology_of_exact _ _ _, } }
end
.

open opposite

namespace homological_complex

@[simps]
def op (X : homological_complex C c) : homological_complex Cᵒᵖ c.symm :=
{ X := λ i, op (X.X i),
  d := λ i j, (X.d j i).op,
  shape' := λ i j hij, by { rw [X.shape j i hij, op_zero], },
  d_comp_d' := by { intros, rw [← op_comp, X.d_comp_d, op_zero], } }

@[simps]
def unop (X : homological_complex Cᵒᵖ c) : homological_complex C c.symm :=
{ X := λ i, unop (X.X i),
  d := λ i j, (X.d j i).unop,
  shape' := λ i j hij, by { rw [X.shape j i hij, unop_zero], },
  d_comp_d' := by { intros, rw [← unop_comp, X.d_comp_d, unop_zero], } }

end homological_complex

@[to_additive]
lemma subgroup.comap_eq_iff {A B : Type*} [comm_group A] [comm_group B] (f : A ≃* B)
  (C : subgroup A) (D : subgroup B) :
  D.comap f.to_monoid_hom = C ↔ C.comap f.symm.to_monoid_hom = D :=
begin
  split; rintro rfl; ext,
  { simp only [subgroup.mem_comap, mul_equiv.coe_to_monoid_hom, mul_equiv.apply_symm_apply], },
  { simp only [subgroup.mem_comap, mul_equiv.coe_to_monoid_hom, mul_equiv.symm_apply_apply], }
end

@[to_additive] noncomputable
def mul_equiv.surjective_congr {A B C D : Type*}
  [comm_group A] [comm_group B] [comm_group C] [comm_group D]
  (e : A ≃* B) (f : A →* C) (g : B →* D)
  (hf : function.surjective f) (hg : function.surjective g)
  (he : g.ker.comap e.to_monoid_hom = f.ker) :
C ≃* D :=
{ to_fun := f.lift_of_surjective hf ⟨g.comp e.to_monoid_hom, λ x hx,
  by { rw ← he at hx, exact hx }⟩,
  inv_fun := g.lift_of_surjective hg ⟨f.comp e.symm.to_monoid_hom, λ x hx,
  by { rw subgroup.comap_eq_iff at he, rw ← he at hx, exact hx, }⟩,
  left_inv := λ x, begin
    obtain ⟨x, rfl⟩ := hf x,
    delta monoid_hom.lift_of_surjective,
    simp only [monoid_hom.lift_of_right_inverse_comp_apply, subtype.coe_mk, monoid_hom.comp_apply],
    convert monoid_hom.lift_of_right_inverse_comp_apply _ _ _ _ (e.to_monoid_hom x) using 1,
    exact f.congr_arg (e.symm_apply_apply x).symm,
  end,
  right_inv := λ x, begin
    obtain ⟨x, rfl⟩ := hg x,
    delta monoid_hom.lift_of_surjective,
    simp only [monoid_hom.lift_of_right_inverse_comp_apply, subtype.coe_mk, monoid_hom.comp_apply],
    convert monoid_hom.lift_of_right_inverse_comp_apply _ _ _ _ (e.symm.to_monoid_hom x) using 1,
    exact g.congr_arg (e.apply_symm_apply x).symm,
  end,
  map_mul' := λ x y, monoid_hom.map_mul _ _ _ }

@[to_additive]
def mul_equiv.quotient_congr {A B : Type*} [comm_group A] [comm_group B] (f : A ≃* B)
  (C : subgroup A) (D : subgroup B) (h : D.comap f.to_monoid_hom = C) :
A ⧸ C ≃* B ⧸ D :=
{ to_fun := quotient_group.map _ _ f.to_monoid_hom h.ge,
  inv_fun := quotient_group.map _ _ f.symm.to_monoid_hom
  begin
    refine le_of_eq _, subst h, ext,
    simp only [subgroup.mem_comap, mul_equiv.coe_to_monoid_hom, mul_equiv.apply_symm_apply],
  end,
  left_inv := λ x, begin
    induction x using quotient_group.induction_on,
    erw [quotient_group.map_coe, f.symm_apply_apply],
    refl,
  end,
  right_inv := λ x, begin
    induction x using quotient_group.induction_on,
    erw [quotient_group.map_coe, f.apply_symm_apply],
    refl,
  end,
  map_mul' := λ x y, monoid_hom.map_mul _ _ _ }
.

attribute [elementwise] limits.kernel.lift_ι iso.hom_inv_id

protected noncomputable
def AddCommGroup.homology_iso {A B C : AddCommGroup.{u}} (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0) :
  homology f g w ≅ AddCommGroup.of (g.ker ⧸ (f.range.comap g.ker.subtype)) :=
begin
  refine homology_iso_cokernel_lift f g w ≪≫
    AddCommGroup.cokernel_iso_quotient _ ≪≫
    add_equiv_iso_AddCommGroup_iso.hom _,
  refine add_equiv.quotient_congr _ _ _ _,
  { exact add_equiv_iso_AddCommGroup_iso.inv (AddCommGroup.kernel_iso_ker _) },
  rw add_subgroup.comap_eq_iff,
  show add_subgroup.comap (AddCommGroup.kernel_iso_ker g).inv
    (add_monoid_hom.range (limits.kernel.lift g f w)) =
    add_subgroup.comap (add_monoid_hom.ker g).subtype (add_monoid_hom.range f),
  dsimp only [AddCommGroup.kernel_iso_ker],
  have : function.injective (λ x, limits.kernel.ι g x),
  { rw [← AddCommGroup.kernel_iso_ker_hom_comp_subtype, coe_comp],
    have : function.injective (g.ker.subtype) := subtype.val_injective,
    refine this.comp _,
    refine function.has_left_inverse.injective _,
    refine ⟨(AddCommGroup.kernel_iso_ker _).inv, _⟩,
    intro y, refine category_theory.iso.hom_inv_id_apply (AddCommGroup.kernel_iso_ker g) y, },
  ext ⟨x, hx⟩,
  simp only [add_subgroup.mem_comap, add_monoid_hom.mem_range, add_subgroup.coe_subtype,
    subtype.coe_mk, ← this.eq_iff, category_theory.limits.kernel.lift_ι_apply],
end
.

def homotopy_category.quotient_map_hom (A B : homological_complex C c) :
  (A ⟶ B) →+ ((homotopy_category.quotient C c).obj A ⟶ (homotopy_category.quotient C c).obj B) :=
add_monoid_hom.mk' (λ f, (homotopy_category.quotient C c).map f) $ λ f g, rfl

lemma quot.mk_surjective {X : Type*} (r : X → X → Prop) :
  function.surjective (quot.mk r) :=
λ x, quot.induction_on x $ λ x, ⟨x, rfl⟩

open category_theory.limits

noncomputable
def bounded_homotopy_category.hom_shift_single_iso
  (P : bounded_homotopy_category C) (B : C) (i : ℤ) :
  AddCommGroup.of (P ⟶ (shift_functor (bounded_homotopy_category C) i).obj
    ((bounded_homotopy_category.single 0).obj B)) ≅
  (((preadditive_yoneda.obj B).map_homological_complex _).obj P.val.as.op).homology (-i) :=
begin
  refine _ ≪≫ (homology_iso _ (-i+1) (-i) (-i-1) _ _).symm,
  rotate, { dsimp, refl }, { dsimp, exact sub_add_cancel _ _ },
  refine add_equiv_iso_AddCommGroup_iso.hom _ ≪≫ (AddCommGroup.homology_iso _ _ _).symm,
  refine add_equiv.surjective_congr _
    (homotopy_category.quotient_map_hom _ _)
    (quotient_add_group.mk' _) (quot.mk_surjective _) (quot.mk_surjective _) _,
  refine
  { to_fun := by sorry; begin
      intro f,
      refine ⟨_, _⟩,
      { refine f.f (-i) ≫ _,
        dsimp [bounded_homotopy_category.shift_functor_obj_val, bounded_homotopy_category.single],
        simp only [add_left_neg, eq_self_iff_true, if_true],
        exact 𝟙 B, },
      { simp only [add_left_neg, eq_self_iff_true, ite_eq_left_iff, not_true, forall_false_left,
          congr_arg_mpr_hom_left, category.comp_id, id.def, functor.map_homological_complex_obj_d,
          homological_complex.op_d, add_monoid_hom.mem_ker],
        erw [preadditive_yoneda_obj_map_apply, quiver.hom.unop_op, ← category.assoc,
          ← homological_complex.hom.comm],
        dsimp [bounded_homotopy_category.single],
        simp only [smul_zero, comp_zero, zero_comp], }
    end,
    inv_fun := begin
      intro f,
      refine ((shift_equiv _ i).symm.to_adjunction.hom_equiv P.val.as _) _,
      refine { f := λ j, _, comm' := _ },
      { dsimp [bounded_homotopy_category.shift_functor_obj_val, bounded_homotopy_category.single],
        rcases j with ((_|j)|j),
        { dsimp, refine eq_to_hom _ ≫ f.1, rw zero_add, refl },
        { exact 0 },
        { exact 0 } },
      { intros j k hjk, dsimp at hjk, subst k,
        rcases j with ((_|j)|(_|j)),
        { dsimp, refine comp_zero.trans comp_zero.symm, },
        { dsimp, refine comp_zero.trans comp_zero.symm, },
        { refine comp_zero.trans _,
          cases f with f hf,
          change P.val.as.d (-i - 1) (-i) ≫ f = 0 at hf,
          dsimp, simp only [int.neg_one_pow_neg, linear.smul_comp],
          convert (smul_zero _).symm using 2,
          have H1 : (complex_shape.up ℤ).rel (-[1+ 0] + -i) (-[1+ 0] + 1 + -i),
          { dsimp, rw add_right_comm, },
          have H2 : (complex_shape.up ℤ).rel (-i - 1) (-[1+ 0] + 1 + -i),
          { dsimp, simp only [sub_add_cancel, self_eq_add_left], refl },
          have H3 : (complex_shape.up ℤ).rel (-i - 1) (-i),
          { dsimp, rw sub_add_cancel, },
          rw [← homological_complex.eq_to_hom_comp_d _ H1 H2,
              ← homological_complex.d_comp_eq_to_hom _ H2 H3],
          simp only [category.assoc],
          convert comp_zero using 2,
          convert hf using 2,
          rw ← is_iso.eq_inv_comp,
          simp only [inv_eq_to_hom],
          refl, },
        { dsimp, refine comp_zero.trans comp_zero.symm, }, }
    end,
    left_inv := _,
    right_inv := _,
    map_add' := _ },
  all_goals { sorry },
end

noncomputable
def Ext'_iso (A : Cᵒᵖ) (B : C) (i : ℤ) (P : chain_complex C ℕ)
  (π : P ⟶ (chain_complex.single₀ C).obj A.unop)
  (hP : P.is_projective_resolution A.unop π) :
  ((Ext' i).obj A).obj B ≅
  (((preadditive_yoneda.obj B).map_homological_complex _).obj
    ((homological_complex.embed complex_shape.embedding.nat_down_int_up).obj P).op).homology (-i) :=
begin
  dsimp only [Ext', functor.comp_obj, functor.op_obj, functor.flip_obj_obj],
  haveI := chain_complex.to_bounded_homotopy_category.is_K_projective P A.unop π hP,
  haveI : is_quasi_iso (chain_complex.to_bounded_homotopy_category.map π) := hP.is_quasi_iso_embed,
  refine (bounded_homotopy_category.Ext_iso i
    (chain_complex.to_bounded_homotopy_category.obj P)
    _ _ (chain_complex.to_bounded_homotopy_category.map π ≫ _)) ≪≫
    bounded_homotopy_category.hom_shift_single_iso _ B i,
  { exact ((homotopy_category.quotient _ _).map_iso $
      (chain_complex.single₀_comp_embed_iso_single).app A.unop).hom, },
  { apply_instance },
end

lemma AddCommGroup.is_zero_of_eq (A : AddCommGroup) (h : ∀ x y : A, x = y) :
  is_zero A :=
{ eq_zero_of_src := λ B f, by { ext, cases h x 0, exact f.map_zero },
  eq_zero_of_tgt := λ B f, by { ext, exact h _ _ } }

lemma category_theory.ProjectiveResolution.is_projective_resolution
  {A : C} (P : ProjectiveResolution A) :
  P.complex.is_projective_resolution _ P.π :=
{ projective := P.projective,
  exact₀ := P.exact₀,
  exact := P.exact,
  epi := ProjectiveResolution.f.category_theory.epi P 0 }

lemma Ext_is_zero_of_neg (A : Cᵒᵖ) (B : C) (i : ℤ) (hi : i < 0) :
  is_zero (((Ext' i).obj A).obj B) :=
begin
  let P := ProjectiveResolution.of A.unop,
  refine is_zero_of_iso_of_zero _ (Ext'_iso _ _ i P.complex P.π P.is_projective_resolution).symm,
  rcases i with (i|i),
  { exfalso, revert hi, dec_trivial },
  refine is_zero.homology_is_zero _ _ _ _,
  refine AddCommGroup.is_zero_of_eq _ _,
  intros f g,
  ext,
end

namespace AddCommGroup

-- We only need `G` to preserve epimorphisms, but we don't have such a class.
lemma preserves_projectives {C D : Type*} [category C] [category.{v} D] {F : C ⥤ D} {G : D ⥤ C}
  (adj : F ⊣ G) [preserves_colimits_of_shape walking_span.{v} G] (P : C) [projective P] :
    projective (F.obj P) :=
begin
  constructor,
  intros,
  resetI,
  use (adj.hom_equiv _ _).symm (projective.factor_thru (adj.hom_equiv _ _ f) (G.map e)),
  rw [← adj.hom_equiv_naturality_right_symm, projective.factor_thru_comp, equiv.symm_apply_apply],
end

instance {C D : Type*} [category C] [category D] {F : C ⥤ D}
  {G : D ⥤ C} (adj : F ⊣ G) [faithful G] (X : D) : epi (adj.counit.app X) :=
begin
  haveI : split_epi (G.map (adj.counit.app X)) := ⟨_, adj.right_triangle_components⟩,
  exact faithful_reflects_epi G infer_instance
end

lemma enough_projectives_of_adjoint {C D : Type*} [category C] [category.{v} D] {F : C ⥤ D}
  {G : D ⥤ C} (adj : F ⊣ G) [preserves_colimits_of_shape walking_span.{v} G] [faithful G]
  [enough_projectives C] : enough_projectives D :=
begin
  haveI : is_left_adjoint F := ⟨_, adj⟩,
  constructor,
  intro X,
  refine ⟨⟨_, preserves_projectives adj _, (adj.hom_equiv _ _).symm (projective.π (G.obj X)), _⟩⟩,
  dsimp,
  rw adjunction.hom_equiv_counit,
  exact epi_comp _ _,
end

instance : enough_projectives AddCommGroup.{u} :=
enough_projectives_of_adjoint
  (functor.as_equivalence (forget₂ (Module ℤ) AddCommGroup)).to_adjunction

lemma Ext_is_zero_of_one_lt
  (A : AddCommGroup.{u}ᵒᵖ) (B : AddCommGroup.{u}) (i : ℤ) (hi : i > 1) :
  is_zero (((Ext' i).obj A).obj B) :=
begin
  induction A,
  rcases A with ⟨A, _Ainst⟩, resetI,
  let := Ext'_iso (op $AddCommGroup.of A) B i,
  dsimp at this,
  refine is_zero_of_iso_of_zero _ (this _ _ (two_step_resolution_ab_projective A)).symm,
  rcases i with ((_|_|i)|i),
  { exfalso, revert hi, dec_trivial },
  { exfalso, revert hi, dec_trivial },
  swap,
  { exfalso, revert hi, dec_trivial },
  refine is_zero.homology_is_zero _ _ _ _,
  refine AddCommGroup.is_zero_of_eq _ _,
  intros f g,
  apply category_theory.limits.has_zero_object.from_zero_ext,
end

noncomputable theory
variable (n : ℕ)

def zmod_resolution : chain_complex AddCommGroup ℕ :=
chain_complex.mk' (of ℤ) (of ℤ) (n • 𝟙 _) (λ _, ⟨0, 0, zero_comp⟩)

example : (zmod_resolution n).X 0 = of ℤ := rfl

def zmod_resolution_pi_f :
  Π (i : ℕ), (zmod_resolution n).X i ⟶ ((chain_complex.single₀ AddCommGroup).obj (of $ zmod n)).X i
| 0     := show of ℤ ⟶ of (zmod n), from @int.cast_add_hom _ _ ⟨(1 : zmod n)⟩
| (i+1) := 0

def zmod_resolution_pi :
  zmod_resolution n ⟶ (chain_complex.single₀ AddCommGroup).obj (of $ zmod n) :=
{ f := zmod_resolution_pi_f n,
  comm' := begin
    rintros i ⟨_|j⟩ (rfl : _ = _),
    { ext k, dsimp [zmod_resolution_pi_f, zmod_resolution],
      simp only [zero_apply, fin.coe_zero, comp_apply, int.coe_cast_add_hom],
      simp only [chain_complex.mk'_d_1_0, add_monoid_hom.coe_smul, pi.smul_apply, id_apply,
        nsmul_one, int.nat_cast_eq_coe_nat, int.coe_nat_bit0, int.coe_nat_succ, int.coe_nat_zero,
        zero_add, int.cast_bit0, int.cast_one],
      exact (zmod.nat_cast_self n).symm },
    { exact comp_zero.trans comp_zero.symm }
  end }

instance : projective (AddCommGroup.of ℤ) :=
preserves_projectives (functor.as_equivalence (forget₂ (Module ℤ) AddCommGroup)).to_adjunction
  (Module.of ℤ ℤ)

instance exact_zmod_nsmul_cast :
  exact (n • 𝟙 (of ℤ)) (AddCommGroup.of_hom $ int.cast_add_hom (zmod n)) :=
begin
  rw AddCommGroup.exact_iff,
  erw zmod.ker_int_cast_add_hom,
  ext,
  apply exists_congr,
  rintro (a : ℤ),
  change n • a = x ↔ a * (n : ℤ) = x,
  rw mul_comm,
  norm_num,
end

lemma zmod_resolution_is_resolution (hn : n ≠ 0) :
  (zmod_resolution n).is_projective_resolution (of (zmod n)) (zmod_resolution_pi n) :=
begin
  constructor,
  { rintro (_|_|_|_),
    { show projective (AddCommGroup.of ℤ), by apply_instance },
    { show projective (AddCommGroup.of ℤ), by apply_instance },
    { show projective (0 : AddCommGroup), by apply_instance },
    { show projective (0 : AddCommGroup), by apply_instance } },
  { dsimp [zmod_resolution_pi, zmod_resolution_pi_f, zmod_resolution],
    rw chain_complex.mk'_d_1_0,
    exact AddCommGroup.exact_zmod_nsmul_cast n },
  { intro i,
    dsimp [zmod_resolution, chain_complex.mk', chain_complex.mk, chain_complex.of],
    rw [if_pos rfl, if_pos rfl, category.id_comp, category.id_comp],
    rcases i with (_|_|_),
    { show exact 0 (n • 𝟙 (of ℤ)),
      rw [(abelian.tfae_mono 0 (n • 𝟙 (of ℤ))).out 2 0, AddCommGroup.mono_iff_injective],
      rintros (x : ℤ) (y : ℤ) (e : n • x = n • y),
      norm_num at e,
      exact e.resolve_right hn },
    { show exact 0 0, apply_instance },
    { show exact 0 0, apply_instance } },
  { dsimp [zmod_resolution_pi, zmod_resolution_pi_f],
    rw AddCommGroup.epi_iff_surjective,
    rintro (x : zmod n),
    exact ⟨(x : ℤ), by norm_num⟩ }
end

lemma zmod.nsmul_eq_zero (k : zmod n) : n • k = 0 := by norm_num

@[simps] def add_subgroup.equiv_top (A : Type*) [add_comm_group A] :
  A ≃+ (⊤ : add_subgroup A) :=
{ to_fun := λ x, ⟨x, add_subgroup.mem_top _⟩,
  inv_fun := λ x, x,
  left_inv := λ x, rfl,
  right_inv := by { rintro ⟨x, hx⟩, refl },
  map_add' := λ x y, rfl }

def Ext_zmod (hn : n ≠ 0) :
  ((Ext' 1).obj (op $ of $ zmod n)).obj (of $ zmod n) ≅ of (zmod n) :=
begin
  refine Ext'_iso (op $ of $ zmod n) (of $ zmod n) 1 (zmod_resolution n) (zmod_resolution_pi n)
    (zmod_resolution_is_resolution n hn) ≪≫
      (homology_iso _ 0 (-1) (-2) rfl rfl) ≪≫ _,
  refine (AddCommGroup.homology_iso _ _ _) ≪≫ _,
  refine add_equiv_iso_AddCommGroup_iso.hom _,
  refine add_equiv.surjective_congr _ (quotient_add_group.mk' _) (add_monoid_hom.id _)
    (quot.mk_surjective _) function.surjective_id _,
  refine (add_equiv.add_subgroup_congr _).trans _,
  { exact ⊤ },
  { convert add_monoid_hom.ker_zero using 2,
    refine is_zero.eq_of_tgt _ _ _,
    refine AddCommGroup.is_zero_of_eq _ _,
    intros f g,
    apply category_theory.limits.has_zero_object.from_zero_ext, },
  { refine (add_subgroup.equiv_top _).symm.trans (zmultiples_add_hom _).symm, },
  { simp only [add_monoid_hom.ker_zero, quotient_add_group.ker_mk,
     functor.map_homological_complex_obj_d, homological_complex.op_d],
    ext ⟨f, hf⟩,
    simp only [add_subgroup.mem_comap, add_equiv.coe_to_add_monoid_hom, add_equiv.coe_trans,
      function.comp_app, zmultiples_add_hom_symm_apply, add_subgroup.coe_subtype,
      add_subgroup.coe_mk, add_monoid_hom.mem_range],
    simp only [add_subgroup.equiv_top_symm_apply, add_monoid_hom.mem_ker],
    dsimp [add_equiv.add_subgroup_congr, zmod_resolution],
    split,
    { intro hf1, refine ⟨0, comp_zero.trans _⟩, ext1, exact hf1.symm },
    { intro H, cases H with g hg, rw [← hg, coe_comp],
      convert g.map_nsmul _ _ using 1,
      simp only [eq_to_hom_refl, id_apply, zmod.nsmul_eq_zero] } }
end


end AddCommGroup
