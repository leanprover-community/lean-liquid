import data.zmod.basic

import for_mathlib.complex_extend
import for_mathlib.projectives
import for_mathlib.two_step_resolution
import for_mathlib.hom_single_iso
import for_mathlib.homological_complex_op

.

universes v u

open category_theory homotopy_category

variables {C : Type u} {ι : Type*} [category.{v} C] [abelian C] {c : complex_shape ι}

open_locale zero_object

instance projective_zero : projective (0 : C) :=
{ factors := λ E X f e he, ⟨0, by ext⟩ }

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

lemma chain_complex.bounded_by_one (P : chain_complex C ℕ) :
  ((homological_complex.embed complex_shape.embedding.nat_down_int_up ⋙
      quotient C (complex_shape.up ℤ)).obj P).bounded_by 1 :=
begin
  rintro ((_|i)|i) h,
  { exfalso, revert h, dec_trivial },
  { exact limits.is_zero_zero _ },
  { exfalso, revert h, dec_trivial }
end

instance chain_complex.is_bounded_above (P : chain_complex C ℕ) :
  ((homological_complex.embed complex_shape.embedding.nat_down_int_up ⋙
      quotient C (complex_shape.up ℤ)).obj P).is_bounded_above :=
⟨⟨1, chain_complex.bounded_by_one _⟩⟩

/-- The functor from ℕ-indexed chain complexes to bounded-above ℤ-indexed cochain complexes
sending `C₀ ← C₁ ← ...` to `... ⟶ C₁ ⟶ C₀ ⟶ 0 ⟶ ...` -/
@[simps obj obj_val map]
noncomputable def chain_complex.to_bounded_homotopy_category :
  chain_complex C ℕ ⥤ bounded_homotopy_category C :=
{ obj := λ P,
  { val := (homological_complex.embed (complex_shape.embedding.nat_down_int_up) ⋙
      homotopy_category.quotient C _).obj P,
    bdd := by apply chain_complex.is_bounded_above },
  map := λ P Q f, (homological_complex.embed (complex_shape.embedding.nat_down_int_up) ⋙
      homotopy_category.quotient C _).map f,
  map_id' := λ P, (homological_complex.embed (complex_shape.embedding.nat_down_int_up) ⋙
      homotopy_category.quotient C _).map_id P,
  map_comp' := λ P Q R f g, (homological_complex.embed (complex_shape.embedding.nat_down_int_up) ⋙
      homotopy_category.quotient C _).map_comp f g }

lemma chain_complex.to_bounded_homotopy_category.is_K_projective [enough_projectives C]
  (P : chain_complex C ℕ) (A : C) (π : P ⟶ (chain_complex.single₀ C).obj A)
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
    { intro h, exact limits.is_zero_zero _ },
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
  (h : exact f g) [epi g] : is_iso (homology.desc' f (0 : Y ⟶ W) limits.comp_zero
    (limits.kernel_zero_iso_source.hom ≫ g) (by simp [h.w])) :=
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
    swap 2, convert @@homology.desc_zero_is_iso_of_exact_of_epi _ _ _ _ hP.exact₀ hP.epi using 1,
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
      simp only [homology.π'_desc', category.comp_id, homological_complex.hom.sq_from_left,
        limits.kernel_subobject_arrow_assoc, homology.π_desc, homology.map_desc,
        limits.kernel_subobject_map_arrow_assoc, arrow.iso_mk_hom_left,
        limits.kernel_subobject_map_arrow],
      dsimp [chain_complex.single₀_comp_embed_iso_single,
        chain_complex.single₀_comp_embed_iso_single_component],
      simp,
      apply_instance },
    { apply_instance } },
  { refine limits.is_zero.is_iso _ _ _; refine exact.homology_is_zero _ _ (exact_of_zero _ _), },
  { refine limits.is_zero.is_iso _ _ _,
    { refine limits.is_zero_of_iso_of_zero _ (homology_iso _ (-[1+i.succ] : ℤ) _ (-i : ℤ) _ _).symm,
      rotate,
      { dsimp, refl, },
      { dsimp, simp only [int.neg_succ_of_nat_eq', sub_add_cancel], },
      refine exact.homology_is_zero _ _ _,
      cases i; exact (hP.exact _), },
    { refine limits.is_zero_of_iso_of_zero _ (homology_iso _ (-[1+i.succ] : ℤ) _ (-i : ℤ) _ _).symm,
      rotate,
      { dsimp, refl, },
      { dsimp, simp only [int.neg_succ_of_nat_eq', sub_add_cancel], },
      refine exact.homology_is_zero _ _ (exact_of_zero _ _), } }
end
.

open opposite
open category_theory.limits

@[simp]
lemma _root_.category_theory.equivalence.symm_to_adjunction_counit {C D : Type*} [category C]
  [category D] (e : C ≌ D) : e.symm.to_adjunction.counit = e.unit_inv := rfl

@[simp]
lemma _root_.homological_complex.shift_equiv_unit_app (i j : ℤ) (X : cochain_complex C ℤ) :
  homological_complex.hom.f ((shift_equiv _ i).unit.app X) j = (X.X_eq_to_iso $ by simp).hom :=
begin
  dsimp [shift_equiv, unit_of_tensor_iso_unit],
  simp only [homological_complex.X_eq_to_iso, eq_to_hom_map, eq_to_hom_app, eq_to_iso.hom,
    homological_complex.eq_to_hom_f, eq_to_hom_trans, homological_complex.shift_μ_inv_app_f],
end

@[simp]
lemma _root_.homological_complex.shift_equiv_unit_inv_app (i j : ℤ) (X : cochain_complex C ℤ) :
  homological_complex.hom.f ((shift_equiv _ i).unit_inv.app X) j = (X.X_eq_to_iso $ by simp).hom :=
begin
  dsimp [shift_equiv, unit_of_tensor_iso_unit],
  simp only [homological_complex.X_eq_to_iso, eq_to_hom_map, eq_to_hom_app, eq_to_iso.hom,
    homological_complex.eq_to_hom_f, homological_complex.shift_ε_inv_app_f, eq_to_hom_trans],
end

@[simp]
lemma _root_.category_theory.equivalence.symm_to_adjunction_unit {C D : Type*} [category C]
  [category D] (e : C ≌ D) : e.symm.to_adjunction.unit = e.counit_inv := rfl

@[simp]
lemma _root_.homological_complex.shift_equiv_counit_app (i j : ℤ) (X : cochain_complex C ℤ) :
  homological_complex.hom.f ((shift_equiv _ i).counit.app X) j = (X.X_eq_to_iso $ by simp).hom :=
begin
  dsimp [shift_equiv, unit_of_tensor_iso_unit],
  simp only [homological_complex.X_eq_to_iso, eq_to_hom_map, eq_to_hom_app, eq_to_iso.hom,
    homological_complex.eq_to_hom_f, homological_complex.shift_ε_inv_app_f, eq_to_hom_trans],
end

@[simp]
lemma _root_.homological_complex.shift_equiv_counit_inv_app (i j : ℤ) (X : cochain_complex C ℤ) :
  homological_complex.hom.f ((shift_equiv _ i).counit_inv.app X) j = (X.X_eq_to_iso $ by simp).hom :=
begin
  dsimp [shift_equiv, unit_of_tensor_iso_unit],
  simpa only [homological_complex.X_eq_to_iso, eq_to_hom_map, eq_to_hom_app, eq_to_iso.hom,
    add_neg_equiv_counit_iso_inv, nat_trans.comp_app, homological_complex.comp_f,
    homological_complex.shift_ε_hom_app_f, homological_complex.eq_to_hom_f,
    homological_complex.shift_μ_inv_app_f, eq_to_hom_trans],
end

variable [enough_projectives C]

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
    (preadditive_yoneda.map_iso _).app (op (chain_complex.to_bounded_homotopy_category.obj P)) ≪≫
      bounded_homotopy_category.hom_single_iso _ B (-i),
  { exact ((homotopy_category.quotient _ _).map_iso $
      (chain_complex.single₀_comp_embed_iso_single).app A.unop).hom, },
  { apply_instance },
  { exact (bounded_homotopy_category.shift_single_iso 0 i).app B ≪≫ eq_to_iso (by rw zero_sub) }
end

lemma AddCommGroup.is_zero_of_eq (A : AddCommGroup) (h : ∀ x y : A, x = y) :
  is_zero A :=
begin
  rw is_zero_iff_id_eq_zero,
  ext,
  apply h,
end

lemma category_theory.ProjectiveResolution.is_projective_resolution
  {A : C} (P : ProjectiveResolution A) :
  P.complex.is_projective_resolution _ P.π :=
{ projective := P.projective,
  exact₀ := P.exact₀,
  exact := P.exact,
  epi := ProjectiveResolution.f.category_theory.epi P 0 }

lemma Ext'_is_zero_of_neg (A : Cᵒᵖ) (B : C) (i : ℤ) (hi : i < 0) :
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

section
open bounded_homotopy_category

lemma Ext_single_right_is_zero
  (A : homotopy_category C (complex_shape.up ℤ)) (B : C)
  (i j k : ℤ)
  (hA : A.bounded_by i) [A.is_bounded_above]
  (hijk : i + j ≤ k) :
  is_zero (((Ext j).obj (op ⟨A⟩)).obj ((bounded_homotopy_category.single _ k).obj B)) :=
begin
  obtain ⟨P, H1, H2, f, H3, H4⟩ :=
    exists_bounded_K_projective_replacement_of_bounded _ _ hA,
  have H5 : P.is_bounded_above := ⟨⟨i, H2⟩⟩,
  resetI,
  refine is_zero_of_iso_of_zero _ (Ext_iso j ⟨P⟩ _ _ _).symm,
  swap, { exact f }, swap, { exact H3 },
  refine AddCommGroup.is_zero_of_eq _ _,
  rintro (φ ψ : P ⟶ _),
  rw [← quotient_map_out φ, ← quotient_map_out ψ],
  congr' 1,
  ext n,
  by_cases hn : i ≤ n,
  { apply (H2 n hn).eq_of_src },
  { apply is_zero.eq_of_tgt,
    dsimp [bounded_homotopy_category.single],
    rw if_neg, { exact is_zero_zero _ },
    linarith only [hijk, hn], }
end

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

-- move me (the rest of the file)

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
        nsmul_one, int.coe_nat_bit0, int.coe_nat_succ, int.coe_nat_zero,
        zero_add, int.cast_bit0, int.cast_one],
      exact (zmod.nat_cast_self n).symm },
    { exact comp_zero.trans comp_zero.symm }
  end }

instance : projective (AddCommGroup.of ℤ) :=
preserves_projectives (functor.as_equivalence (forget₂ (Module ℤ) AddCommGroup)).to_adjunction
  (Module.of ℤ ℤ)

lemma exact_zmod_nsmul_cast :
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
    { show exact 0 0, apply exact_of_zero },
    { show exact 0 0, apply exact_of_zero } },
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

end AddCommGroup
