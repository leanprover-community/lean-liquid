import category_theory.sites.left_exact
import for_mathlib.AddCommGroup.kernels
import for_mathlib.abelian_category
import for_mathlib.abelian_sheaves.main
import algebra.category.Group.filtered_colimits
import algebra.group.ulift

namespace category_theory.grothendieck_topology

open category_theory
open category_theory.limits
open opposite

universe u
variables {C : Type (u+1)} [category.{u} C] (J : grothendieck_topology C)
variables {F : Cᵒᵖ ⥤ Ab.{u+1}} {G : Sheaf J Ab.{u+1}}

@[simps]
def kernel_fork_point (η : F ⟶ G.val) : Cᵒᵖ ⥤ Ab.{u+1} :=
{ obj := λ X, AddCommGroup.of (η.app X).ker,
  map := λ X Y f,
  { to_fun := λ t, ⟨F.map f t.1, begin
      change (_ ≫ η.app Y) _ = 0, rw nat_trans.naturality,
      rcases t with ⟨t, (ht : η.app X t = 0)⟩, dsimp,
      simp [comp_apply, ht],
    end⟩,
    map_zero' := by { ext, apply add_monoid_hom.map_zero, },
    map_add' := by { intros, ext, apply add_monoid_hom.map_add } },
  map_id' := λ X, by { ext, simp, },
  map_comp' := λ X Y Z f g, by { ext, simp } }

@[simps]
def kernel_fork_ι (η : F ⟶ G.val) : kernel_fork_point J η ⟶ F :=
{ app := λ T, (η.app _).ker.subtype,
  naturality' := begin
    intros X Y f, ext,
    simp only [comp_apply, add_subgroup.coe_subtype,
      kernel_fork_point_map_apply_coe, subtype.val_eq_coe],
  end }

@[simps]
def kernel_fork (η : F ⟶ G.val) : kernel_fork η :=
kernel_fork.of_ι (kernel_fork_ι _ η)
begin
  ext X ⟨x,hx⟩, simpa using hx,
end

def is_limit_kernel_fork (η : F ⟶ G.val) : is_limit (kernel_fork J η) :=
fork.is_limit.mk _ (λ S,
{ app := λ X,
  { to_fun := λ t, ⟨(S.π.app walking_parallel_pair.zero).app _ t, begin
      change (_ ≫ η.app _) _ = _, rw ← nat_trans.comp_app,
      rw S.condition, simp,
    end⟩,
    map_zero' := by { ext, apply add_monoid_hom.map_zero },
    map_add' := by { intros, ext, apply add_monoid_hom.map_add } },
  naturality' := begin
    intros X Y f, ext,
    simp only [comp_apply, add_monoid_hom.coe_mk,
      add_subgroup.coe_mk, kernel_fork_X_map_apply_coe],
    simpa only [← comp_apply, nat_trans.naturality],
  end }) sorry sorry

noncomputable instance : abelian (Cᵒᵖ ⥤ Ab.{u+1}) :=
functor.abelian.{(u+2) u (u+1)}

noncomputable instance : preserves_limits (forget Ab.{u+1}) := infer_instance

noncomputable instance : preserves_filtered_colimits (forget Ab.{u+1}) := infer_instance

noncomputable
instance sheafification_preserves_finite_limits :
  preserves_finite_limits (J.sheafification Ab.{u+1}) :=
begin
  -- Annoying.
  apply sheafification.category_theory.limits.preserves_finite_limits.{(u+2) u (u+1)},
  apply_instance,
  intros x, apply_instance,
  apply_instance,
  apply_instance,
  apply_instance,
end

theorem sheafify_lift_mono_iff (η : F ⟶ G.val) (K : limits.kernel_fork η)
  (hK : is_limit K) :
  mono (J.sheafify_lift η G.cond) ↔
  is_zero (J.sheafify (K.X)) :=
begin
  rw mono_iff_is_zero_kernel,
  suffices E : kernel (J.sheafify_lift η G.cond) ≅ J.sheafify K.X,
  { split,
    { intros h, exact is_zero_of_iso_of_zero h E },
    { intros h, exact is_zero_of_iso_of_zero h E.symm } },
  refine _ ≪≫ (limit.is_limit _).cone_point_unique_up_to_iso
    (is_limit_of_preserves (J.sheafification _) hK),
  refine has_limit.iso_of_nat_iso _,
  symmetry,
  refine nat_iso.of_components _ _,
  rintro (_|_); dsimp,
  exact iso.refl _,
  haveI : is_iso (J.to_sheafify G.val),
  { apply is_iso_to_sheafify, exact G.2 },
  symmetry,
  exact as_iso (J.to_sheafify G.val),
  rintro (_|_) (_|_) (_|_),
  { dsimp, simp, erw J.sheafify_map_id, refl },
  { dsimp, rw is_iso.comp_inv_eq, simp,
    apply J.sheafify_hom_ext,
    apply_with J.sheafify_is_sheaf { instances := ff },
    any_goals { apply_instance },
    intros X, apply_instance,
    simp only [to_sheafify_naturality_assoc],
    rw [← J.sheafify_map_comp, J.to_sheafify_sheafify_lift] },
  { dsimp,
    simp only [comp_zero, preadditive.is_iso.comp_right_eq_zero],
    apply J.sheafify_hom_ext,
    apply_with J.sheafify_is_sheaf { instances := ff },
    any_goals { apply_instance },
    intros x, apply_instance,
    simp only [comp_zero],
    rw [← J.to_sheafify_naturality, zero_comp] },
  { dsimp, simp only [is_iso.comp_inv_eq],
    simp only [category.assoc, is_iso.eq_inv_comp],
    erw [(parallel_pair _ _).map_id, J.sheafify_map_id],
    dsimp, simp only [category.id_comp, category.comp_id], }
end

lemma is_zero_functor {C A : Type*} [category C] [category A] [abelian A]
  (F : C ⥤ A) (hF : ∀ X, is_zero (F.obj X)) :
  is_zero F :=
begin
  split; intros G f; ext Z : 2,
  { apply (hF Z).eq_of_src, },
  { apply (hF Z).eq_of_tgt, }
end

open_locale zero_object

lemma is_zero_iff {C A : Type*} [category C] [category A] [abelian A] (F : C ⥤ A) :
  is_zero F ↔ ∀ X, is_zero (F.obj X) :=
begin
  refine ⟨_, is_zero_functor _⟩,
  intros hF X,
  let G : C ⥤ A := (category_theory.functor.const C).obj 0,
  have hG : is_zero G := is_zero_functor _ (λ X, is_zero_zero _),
  let e : G ≅ F := hG.iso hF,
  refine is_zero_of_iso_of_zero (is_zero_zero _) (e.app X),
end

lemma is_zero_Ab (X : Ab) (hX : ∀ t : X, t = 0) : is_zero X :=
begin
  split; intros Y f,
  { ext x, rw hX x, exact f.map_zero },
  { ext y, apply hX }
end

lemma is_zero_colimit_of_is_zero {C A : Type*} [category C] [category A] [abelian A] (F : C ⥤ A)
  [has_colimits_of_shape C A] (hF : is_zero F) : is_zero (colimit F) :=
begin
  let G : C ⥤ A := (category_theory.functor.const C).obj (⊥_ _),
  have hG : is_zero G := is_zero_functor _ (λ X, is_zero_initial),
  let e : G ≅ F := hG.iso hF,
  refine is_zero_of_iso_of_zero _ (colim.map_iso e),
  refine is_zero_of_iso_of_zero is_zero_initial colimit_const_initial.symm,
end

lemma is_zero_limit_of_is_zero {C A : Type*} [category C] [category A] [abelian A] (F : C ⥤ A)
  [has_limits_of_shape C A] (hF : is_zero F) : is_zero (limit F) :=
begin
  let G : C ⥤ A := (category_theory.functor.const C).obj (⊤_ _),
  have hG : is_zero G := is_zero_functor _ (λ X, is_zero_terminal),
  let e : G ≅ F := hG.iso hF,
  refine is_zero_of_iso_of_zero _ (lim.map_iso e),
  refine is_zero_of_iso_of_zero is_zero_terminal limit_const_terminal.symm,
end

lemma is_zero_plus_of_is_zero (F : Cᵒᵖ ⥤ Ab.{u+1})
  (hF : is_zero F) : is_zero (J.plus_obj F) :=
begin
  rw is_zero_iff, intros X,
  apply is_zero_colimit_of_is_zero,
  rw is_zero_iff at hF ⊢,
  intros W,
  apply is_zero_limit_of_is_zero,
  rw is_zero_iff, intros P,
  cases P; apply hF,
end

lemma eq_zero_of_exists {J : Type u} [small_category J] [is_filtered J]
  (F : J ⥤ Ab.{u}) (j) (t : F.obj j)
  (ht : ∃ (e : J) (q : j ⟶ e), F.map q t = 0) : colimit.ι F j t = 0 :=
begin
  rcases ht with ⟨e, q, hq⟩,
  rw [← colimit.w F q, comp_apply, hq, map_zero],
end

lemma eq_zero_of_forall {J : Type u} [small_category J]
  (F : J ⥤ Ab.{u}) (t : limit F) (ht : ∀ j, limit.π F j t = 0) : t = 0 :=
begin
  let t' : AddCommGroup.of (free_abelian_group punit) ⟶ limit F :=
    AddCommGroup.of_hom (free_abelian_group.lift $ λ _, t),
  suffices : t' = 0,
  { simpa only [t', AddCommGroup.of_hom, free_abelian_group.lift.of] using
      fun_like.congr_fun this (free_abelian_group.of punit.star), },
  apply limit.hom_ext,
  intro j,
  ext x, cases x,
  simpa only [t', AddCommGroup.of_hom, free_abelian_group.lift.of, comp_apply, map_zero,
    add_monoid_hom.zero_apply] using ht j,
end

lemma is_zero_of_exists_cover (F : Cᵒᵖ ⥤ Ab.{u+1})
  (h : ∀ (B : C) (t : F.obj (op B)), ∃ W : J.cover B,
    ∀ f : W.arrow, F.map f.f.op t = 0) : is_zero (J.sheafify F) :=
begin
  -- This proof is a mess...
  apply is_zero_plus_of_is_zero,
  rw is_zero_iff,
  intros B, tactic.op_induction',
  apply is_zero_Ab,
  intros t,
  obtain ⟨W,y,rfl⟩ := concrete.is_colimit_exists_rep _ (colimit.is_colimit _) t,
  apply eq_zero_of_exists,
  let z := concrete.multiequalizer_equiv _ y,
  choose Ws hWs using λ i, (h _ (z.1 i)),
  let T : J.cover B := W.unop.bind Ws, use (op T),
  use (W.unop.bind_to_base _).op,
  apply_fun concrete.multiequalizer_equiv _, swap, apply_instance,
  ext,
  dsimp, rw add_monoid_hom.map_zero,
  dsimp [diagram],
  simp only [← comp_apply, multiequalizer.lift_ι],
  dsimp [cover.index] at x,
  dsimp only [cover.index] at hWs,
  dsimp [cover.arrow.map],
  cases x with Z x hx, rcases hx with ⟨A,g,f,hf,hA,rfl⟩,
  dsimp at hA ⊢,
  specialize hWs ⟨_,f,hf⟩ ⟨_,g,hA⟩,
  convert hWs,
  dsimp [z],
  simp only [← comp_apply], congr' 2,
  rw ← category.comp_id (multiequalizer.ι ((unop W).index F) {Y := Z, f := g ≫ f, hf := _}),
  let R : W.unop.relation := ⟨_,_,_, g, 𝟙 _, f, g ≫ f, _, _, _⟩,
  symmetry,
  convert multiequalizer.condition (W.unop.index F) R,
  dsimp [cover.index], rw F.map_id, rw category.id_comp,
end

lemma sheafify_lift_mono_of_exists_cover (η : F ⟶ G.val)
  (h : ∀ (B : C) (t : F.obj (op B)) (ht : η.app _ t = 0),
    ∃ W : J.cover B, ∀ f : W.arrow, F.map f.f.op t = 0) :
  mono (J.sheafify_lift η G.cond) :=
begin
  rw sheafify_lift_mono_iff J η (kernel_fork J η) (is_limit_kernel_fork J η),
  apply is_zero_of_exists_cover,
  rintros B ⟨t,ht⟩,
  specialize h B t ht,
  obtain ⟨W,hW⟩ := h,
  use W, intros f,
  ext, apply hW,
end

end category_theory.grothendieck_topology
