import category_theory.sites.left_exact
import for_mathlib.AddCommGroup.kernels
import for_mathlib.abelian_category
import for_mathlib.abelian_sheaves.main
import algebra.category.Group.filtered_colimits

namespace category_theory.grothendieck_topology

open category_theory
open category_theory.limits
open opposite

universe u
variables {C : Type (u+1)} [category.{u} C] (J : grothendieck_topology C)
variables {F : Cᵒᵖ ⥤ Ab.{u+1}} {G : Sheaf J Ab.{u+1}}

def kernel_fork_point (η : F ⟶ G.val) : Cᵒᵖ ⥤ Ab.{u+1} :=
{ obj := λ X, AddCommGroup.of (η.app X).ker,
  map := λ X Y f,
  { to_fun := λ t, ⟨F.map f t.1, sorry⟩,
    map_zero' := sorry,
    map_add' := sorry },
  map_id' := sorry,
  map_comp' := sorry }

def kernel_fork_ι (η : F ⟶ G.val) : kernel_fork_point J η ⟶ F :=
{ app := λ T, (η.app _).ker.subtype,
  naturality' := sorry }

def kernel_fork (η : F ⟶ G.val) : kernel_fork η :=
kernel_fork.of_ι (kernel_fork_ι _ η) sorry

def is_limit_kernel_fork (η : F ⟶ G.val) : is_limit (kernel_fork J η) :=
fork.is_limit.mk _ (λ S,
{ app := λ X,
  { to_fun := λ t, ⟨(S.π.app walking_parallel_pair.zero).app _ t, sorry⟩,
    map_zero' := sorry,
    map_add' := sorry },
  naturality' := sorry }) sorry sorry

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
  sorry,
end

lemma is_zero_of_exists_cover (F : Cᵒᵖ ⥤ Ab.{u+1})
  (h : ∀ (B : C) (t : F.obj (op B)), ∃ W : J.cover B,
    ∀ f : W.arrow, F.map f.f.op t = 0) : is_zero (J.sheafify F) :=
sorry

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
