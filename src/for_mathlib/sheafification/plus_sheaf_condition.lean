import for_mathlib.sheafification.plus
import for_mathlib.sheafification.glue
import for_mathlib.is_iso_iota

namespace category_theory
namespace presheaf

open category_theory.limits opposite

universes w v u
variables {C : Type u} [category.{v} C] {D : Type w} [category.{max v u} D]
  {J : grothendieck_topology C} {P : Cᵒᵖ ⥤ D}

noncomputable theory

def is_limit_of_is_sheaf {X : C} (S : J.cover X) (hP : is_sheaf J P) :
  is_limit (S.multifork P) :=
{ lift := λ (E : multifork _),
    glue _ hP _ _ (S : sieve X) S.condition (S.family_of_elements P E) (S.compatible _ _),
  fac' := begin
    rintros (E : multifork _) (a|b),
    { convert res_glue P hP X E.X S S.condition
        (S.family_of_elements P E) (S.compatible _ _) a.Y a.f a.hf using 1,
      cases a,
      refl },
    { rw ← E.w (walking_multicospan.hom.fst b),
      rw ← (S.multifork P).w (walking_multicospan.hom.fst b),
      simp_rw ← category.assoc,
      congr' 1,
      apply res_glue }
  end,
  uniq' := begin
    rintros (K : multifork _) m hh,
    apply glue_ext P hP X _ S S.condition,
    intros Y f hf,
    specialize hh (walking_multicospan.left ⟨Y,f,hf⟩),
    erw hh,
    rw res_glue P hP X K.X S S.condition _ _ _ f hf,
    refl,
  end }

theorem is_sheaf_iff_multifork : is_sheaf J P ↔ ∀ (X : C) (S : J.cover X),
  nonempty (is_limit (S.multifork P)) :=
begin
  split,
  { intros hP X S,
    refine ⟨is_limit_of_is_sheaf _ hP⟩ },
  { intros h E X S hS x hx,
    let T : J.cover X := ⟨S,hS⟩,
    specialize h _ T,
    obtain ⟨h⟩ := h,
    let K : multifork (T.index P) :=
      multifork.of_ι _ E (λ I, x I.f I.hf) (λ I, hx _ _ _ _ I.w),
    use h.lift K,
    dsimp,
    split,
    { intros Y f hf,
      dsimp,
      apply h.fac K (walking_multicospan.left ⟨Y,f,hf⟩) },
    { intros e he,
      apply h.uniq K,
      rintros (a|b),
      { apply he },
      { rw ← K.w (walking_multicospan.hom.fst b),
        rw ← (T.multifork P).w (walking_multicospan.hom.fst b),
        simp_rw ← category.assoc,
        congr' 1,
        apply he } } }
end

theorem is_sheaf_iff_multiequalizer [has_limits D] :
  is_sheaf J P ↔ ∀ (X : C) (S : J.cover X),
    is_iso (S.to_multiequalizer P) :=
begin
  rw is_sheaf_iff_multifork,
  apply forall_congr (λ X, _),
  apply forall_congr (λ S, _),
  split,
  { rintro ⟨h⟩,
    let e : P.obj (op X) ≅ multiequalizer (S.index P) :=
      h.cone_point_unique_up_to_iso (limit.is_limit _),
    exact (infer_instance : is_iso e.hom) },
  { introsI h,
    constructor,
    apply limits.is_limit.of_iso_limit (limit.is_limit _) (cones.ext _ _),
    swap, {apply (@as_iso _ _ _ _ _ h).symm },
    intros a,
    symmetry,
    erw is_iso.inv_comp_eq,
    change _ = limit.lift _ _ ≫ _,
    simp }
end

theorem is_iso_of_is_sheaf [has_limits D] [has_colimits D] :
  is_sheaf J P → is_iso (J.to_plus_app P) :=
begin
  rw is_sheaf_iff_multiequalizer,
  intros h,
  resetI,
  suffices : ∀ X, is_iso ((J.to_plus_app P).app X),
  { resetI, apply nat_iso.is_iso_of_is_iso_app },
  intros X,
  dsimp,
  suffices : is_iso (colimit.ι (J.diagram P X.unop) (op ⊤)),
  { resetI, apply is_iso.comp_is_iso },
  suffices : ∀ (S T : (J.cover X.unop)ᵒᵖ) (f : S ⟶ T),
    is_iso ((J.diagram P X.unop).map f),
  { resetI, apply is_initial.is_iso_ι,
    suffices : ∀ (Y : (J.cover X.unop)ᵒᵖ), unique ((op ⊤) ⟶ Y),
    { resetI, apply limits.is_initial.of_unique },
    intros Y,
    constructor,
    { tidy },
    { have : Y = op (Y.unop), by simp,
      rw this,
      refine ⟨quiver.hom.op $ hom_of_le $ semilattice_inf_top.le_top _⟩ } },
  intros S T f,
  have : S.unop.to_multiequalizer P ≫ (J.diagram P (X.unop)).map f =
    T.unop.to_multiequalizer P,
  { ext,
    dsimp,
    simpa },
  have : (J.diagram P (X.unop)).map f = inv (S.unop.to_multiequalizer P) ≫
    T.unop.to_multiequalizer P, by simp [← this],
  rw this,
  apply_instance,
end

end presheaf
end category_theory
