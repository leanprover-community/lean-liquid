import category_theory.abelian.projective
import for_mathlib.abelian_category

noncomputable theory

universes v u

open category_theory category_theory.limits

namespace category_theory

/-- `endomorphisms C` is the category whose objects are an object of `C` equipped with an
endomorphism. Morphisms are morphisms between objects which intertwine the endomorphisms. -/
structure endomorphisms (C : Type u) [category.{v} C] :=
(X : C)
(e : End X)

namespace endomorphisms

section category

variables {C : Type u} [category.{v} C]

@[ext] protected structure hom (X Y : endomorphisms C) :=
(f : X.X ⟶ Y.X)
(comm : X.e ≫ f = f ≫ Y.e)

attribute [reassoc, simp] hom.comm

instance (C : Type u) [category.{v} C] : quiver (endomorphisms C) :=
{ hom := λ X Y, hom X Y }

lemma f_injective (X Y : endomorphisms C) : function.injective (hom.f : (X ⟶ Y) → (X.X ⟶ Y.X)) :=
by { intros f g h, ext, exact h }

protected def id (X : endomorphisms C) : X ⟶ X :=
{ f := 𝟙 _,
  comm := by rw [category.comp_id, category.id_comp] }

protected def comp {X Y Z : endomorphisms C} (f : X ⟶ Y) (g : Y ⟶ Z) : X ⟶ Z :=
{ f := f.f ≫ g.f,
  comm := by simp only [hom.comm, hom.comm_assoc, category.assoc] }

instance (C : Type u) [category.{v} C] : category_struct (endomorphisms C) :=
{ id := λ X, X.id,
  comp := λ X Y Z f g, endomorphisms.comp f g }

@[simp] lemma id_f (X : endomorphisms C) : hom.f (𝟙 X) = 𝟙 X.X := rfl

@[simp, reassoc] lemma comp_f {X Y Z : endomorphisms C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  hom.f (f ≫ g) = f.f ≫ g.f := rfl

instance (C : Type u) [category.{v} C] : category (endomorphisms C) :=
{ id_comp' := λ X Y f, by { ext1, simp only [comp_f, id_f, category.id_comp] },
  comp_id' := λ X Y f, by { ext1, simp only [comp_f, id_f, category.comp_id] },
  assoc' := λ X Y Z W f g h, by { ext1, simp only [comp_f, category.assoc] } }

@[simp, reassoc] lemma pow_comm {X Y : endomorphisms C} (f : X ⟶ Y) (n : ℕ) :
  (X.e ^ n : End X.X) ≫ f.f = f.f ≫ (Y.e ^ n : End Y.X) :=
begin
  induction n with n ih,
  { simp only [pow_zero, End.one_def, category.id_comp, category.comp_id] },
  { simp only [nat.succ_eq_add_one, pow_succ, End.mul_def, category.assoc, hom.comm, reassoc_of ih] }
end

@[simps]
protected def forget (C : Type u) [category.{v} C] : endomorphisms C ⥤ C :=
{ obj := λ X, X.X,
  map := λ X Y f, f.f,
  map_id' := λ X, rfl,
  map_comp' := λ X Y Z f g, rfl }

lemma epi_of_epi_f {X Y : endomorphisms C} (f : X ⟶ Y) [epi f.f] : epi f :=
{ left_cancellation := λ Z g h w, begin
    ext, rw [← cancel_epi f.f, ← comp_f, w, comp_f],
  end }

def mk_iso {X Y : endomorphisms C} (e : X.X ≅ Y.X) (h : X.e ≫ e.hom = e.hom ≫ Y.e) : X ≅ Y :=
{ hom := ⟨e.hom, h⟩,
  inv := ⟨e.inv, by rw [e.comp_inv_eq, category.assoc, e.eq_inv_comp, h]⟩,
  hom_inv_id' := by { ext, simp only [comp_f, iso.hom_inv_id, id_f] },
  inv_hom_id' := by { ext, simp only [comp_f, iso.inv_hom_id, id_f] } }

end category

section limits

variables {C : Type u} [category.{v} C]
variables {J : Type v} [small_category J]

@[simps]
def twist_cone {K : J ⥤ endomorphisms C}
  (S : cone (K ⋙ endomorphisms.forget C)) :
  cone (K ⋙ endomorphisms.forget C) :=
{ X := S.X,
  π :=
  { app := λ j, S.π.app j ≫ (K.obj j).e,
    naturality' := begin
      intros i j f,
      dsimp,
      simp only [category.id_comp, category.assoc, hom.comm],
      erw S.w_assoc,
    end } }

abbreviation cone_e {K : J ⥤ endomorphisms C}
  (S : cone (K ⋙ endomorphisms.forget C)) (hS : is_limit S) :
  S.X ⟶ S.X :=
@is_limit.lift J _ C _ (K ⋙ endomorphisms.forget C) S hS (twist_cone S)

@[simps]
protected def cone {K : J ⥤ endomorphisms C}
  (S : cone (K ⋙ endomorphisms.forget C)) (hS : is_limit S) :
  cone K :=
{ X :=
  { X := S.X,
    e := cone_e S hS },
  π :=
  { app := λ j,
    { f := S.π.app _,
      comm := by { dsimp, simp } },
    naturality' := λ i j f, begin
      ext, dsimp, simp, erw S.w,
    end } }

@[simps]
protected def is_limit_cone {K : J ⥤ endomorphisms C}
  (S : cone (K ⋙ endomorphisms.forget C)) (hS : is_limit S) :
  is_limit (endomorphisms.cone S hS) :=
{ lift := λ S,
  { f := hS.lift ⟨S.X.X,
    { app := λ j, (S.π.app _).f,
      naturality' := begin
        intros i j f,
        dsimp,
        simp [← comp_f],
      end }⟩,
    comm := begin
      apply hS.hom_ext, dsimp, simp,
    end },
  fac' := begin
    intros s j, ext, dsimp, simp,
  end,
  uniq' := begin
    intros s m hm, ext, apply hS.hom_ext,
    intros j, specialize hm j, apply_fun (λ e, e.f) at hm,
    dsimp at *, simp [hm],
  end }

.

protected def cone_iso {K : J ⥤ endomorphisms C} (S : cone K)
  (hS : is_limit ((endomorphisms.forget C).map_cone S)) :
  endomorphisms.cone _ hS ≅ S :=
cones.ext
({ hom :=
  { f := 𝟙 _,
    comm := by { apply hS.hom_ext, intros j, dsimp, simp, erw hS.fac, dsimp, simp, } },
  inv :=
  { f := 𝟙 _,
    comm := by { apply hS.hom_ext, intros j, dsimp, simp, erw hS.fac, dsimp, simp } },
  hom_inv_id' := by { ext, dsimp, simp },
  inv_hom_id' := by { ext, dsimp, simp } })
begin
  intros j, ext,
  dsimp, simp,
end

protected def cone_iso' {K : J ⥤ endomorphisms C}
  (S : cone (K ⋙ endomorphisms.forget C)) (hS : is_limit S) :
  (endomorphisms.forget C).map_cone (endomorphisms.cone S hS) ≅ S :=
cones.ext
(iso.refl _)
begin
  intros j,
  dsimp,
  simp,
end

instance has_limit (K : J ⥤ endomorphisms C) [has_limit (K ⋙ endomorphisms.forget C)] :
  has_limit K :=
⟨⟨⟨_, endomorphisms.is_limit_cone _ (limit.is_limit _)⟩⟩⟩

instance has_limits_of_shape [has_limits_of_shape J C] :
  has_limits_of_shape J (endomorphisms C) := ⟨⟩

instance has_limits [has_limits C] : has_limits (endomorphisms C) := ⟨⟩

instance creates_limit (K : J ⥤ endomorphisms C) : creates_limit K (endomorphisms.forget _) :=
{ reflects := λ S hS, is_limit.of_iso_limit (endomorphisms.is_limit_cone _ _)
    (endomorphisms.cone_iso _ hS),
  lifts := λ S hS,
  { lifted_cone := endomorphisms.cone _ hS,
    valid_lift := endomorphisms.cone_iso' _ _ } }

instance preserves_limit (K : J ⥤ endomorphisms C) [has_limit (K ⋙ endomorphisms.forget C)] :
  preserves_limit K (endomorphisms.forget C) :=
category_theory.preserves_limit_of_creates_limit_and_has_limit K (endomorphisms.forget C)

instance preserves_limits_of_shape [has_limits_of_shape J C] :
  preserves_limits_of_shape J (endomorphisms.forget C) := ⟨⟩

instance preserves_limits [has_limits C] : preserves_limits (endomorphisms.forget C) := ⟨⟩

instance [has_finite_limits C] : preserves_finite_limits (endomorphisms.forget C) :=
by { constructor, introsI J hJ1 hJ2, apply_instance }

end limits

section colimits

variables {C : Type u} [category.{v} C]
variables {J : Type v} [small_category J]

@[simps]
def twist_cocone {K : J ⥤ endomorphisms C}
  (S : cocone (K ⋙ endomorphisms.forget C)) :
  cocone (K ⋙ endomorphisms.forget C) :=
{ X := S.X,
  ι :=
  { app := λ j, (K.obj j).e ≫ S.ι.app j,
    naturality' := begin
      intros i j f,
      dsimp,
      simp only [category.comp_id, ← hom.comm_assoc],
      erw S.w,
    end } }

abbreviation cocone_e {K : J ⥤ endomorphisms C}
  (S : cocone (K ⋙ endomorphisms.forget C)) (hS : is_colimit S) :
  S.X ⟶ S.X :=
@is_colimit.desc J _ C _ (K ⋙ endomorphisms.forget C) S hS (twist_cocone S)

@[simps]
protected def cocone {K : J ⥤ endomorphisms C}
  (S : cocone (K ⋙ endomorphisms.forget C)) (hS : is_colimit S) :
  cocone K :=
{ X :=
  { X := S.X,
    e := cocone_e S hS },
  ι :=
  { app := λ j,
    { f := S.ι.app j,
      comm := by { dsimp, simp } },
    naturality' := λ i j f, begin
      ext, dsimp, simp, erw S.w,
    end } }

@[simps]
protected def is_colimit_cocone {K : J ⥤ endomorphisms C}
  (S : cocone (K ⋙ endomorphisms.forget C)) (hS : is_colimit S) :
  is_colimit (endomorphisms.cocone S hS) :=
{ desc := λ S,
  { f := hS.desc ⟨S.X.X,
    { app := λ j, (S.ι.app j).f,
      naturality' := begin
        intros i j f,
        dsimp,
        simp [← comp_f],
      end }⟩,
    comm := begin
      apply hS.hom_ext, dsimp, simp,
    end },
  fac' := begin
    intros s j, ext, dsimp, simp,
  end,
  uniq' := begin
    intros s m hm, ext, apply hS.hom_ext,
    intros j, specialize hm j, apply_fun (λ e, e.f) at hm,
    dsimp at *, simp [hm],
  end }

.

protected def cocone_iso {K : J ⥤ endomorphisms C} (S : cocone K)
  (hS : is_colimit ((endomorphisms.forget C).map_cocone S)) :
  endomorphisms.cocone _ hS ≅ S :=
cocones.ext
({ hom :=
  { f := 𝟙 _,
    comm := by { apply hS.hom_ext, intros j, dsimp, simp, erw hS.fac, dsimp, simp, } },
  inv :=
  { f := 𝟙 _,
    comm := by { apply hS.hom_ext, intros j, dsimp, simp, erw hS.fac, dsimp, simp } },
  hom_inv_id' := by { ext, dsimp, simp },
  inv_hom_id' := by { ext, dsimp, simp } })
begin
  intros j, ext,
  dsimp, simp,
end

protected def cocone_iso' {K : J ⥤ endomorphisms C}
  (S : cocone (K ⋙ endomorphisms.forget C)) (hS : is_colimit S) :
  (endomorphisms.forget C).map_cocone (endomorphisms.cocone S hS) ≅ S :=
cocones.ext
(iso.refl _)
begin
  intros j,
  dsimp,
  simp,
end

instance has_colimit (K : J ⥤ endomorphisms C) [has_colimit (K ⋙ endomorphisms.forget C)] :
  has_colimit K :=
⟨⟨⟨_, endomorphisms.is_colimit_cocone _ (colimit.is_colimit _)⟩⟩⟩

instance has_colimits_of_shape [has_colimits_of_shape J C] :
  has_colimits_of_shape J (endomorphisms C) := ⟨⟩

instance has_colimits [has_colimits C] : has_colimits (endomorphisms C) := ⟨⟩

instance creates_colimit (K : J ⥤ endomorphisms C) : creates_colimit K (endomorphisms.forget _) :=
{ reflects := λ S hS, is_colimit.of_iso_colimit (endomorphisms.is_colimit_cocone _ _)
    (endomorphisms.cocone_iso _ hS),
  lifts := λ S hS,
  { lifted_cocone := endomorphisms.cocone _ hS,
    valid_lift := endomorphisms.cocone_iso' _ _ } }

instance preserves_colimit (K : J ⥤ endomorphisms C) [has_colimit (K ⋙ endomorphisms.forget C)] :
  preserves_colimit K (endomorphisms.forget C) :=
category_theory.preserves_colimit_of_creates_colimit_and_has_colimit K (endomorphisms.forget C)

instance preserves_colimits_of_shape [has_colimits_of_shape J C] :
  preserves_colimits_of_shape J (endomorphisms.forget C) := ⟨⟩

instance preserves_colimits [has_colimits C] : preserves_colimits (endomorphisms.forget C) := ⟨⟩

instance [has_finite_colimits C] : preserves_finite_colimits (endomorphisms.forget C) :=
by { constructor, introsI J hJ1 hJ2, apply_instance }

end colimits

section projectives

variables {C : Type u} [category.{v} C]

section free

variable [has_coproducts_of_shape (ulift.{v} ℕ) C]

/-- `free X` is ⨁ₙX, the direct sum over the naturals, equipped with the endomorphism
sending `(a : X)` in degree `n` to `a` in degree `n+1`. An alternative way to view `free X`
is `X ⨂_{ℤ} ℤ[T]` with the endomorphism given by multiplication by `T`. -/
@[simps]
def free (X : C) : endomorphisms C :=
{ X := ∐ (λ i : ulift.{v} ℕ, X),
  e := sigma.desc $ λ i, sigma.ι (λ i : ulift.{v} ℕ, X) ⟨i.down + 1⟩ }

@[reassoc] lemma free.ι_comp_e (X : C) (i : ulift.{v} ℕ) :
  sigma.ι (λ i : ulift.{v} ℕ, X) i ≫ (free X).e = sigma.ι (λ i : ulift.{v} ℕ, X) ⟨i.down + 1⟩ :=
begin
  dsimp, simp only [colimit.ι_desc, cofan.mk_ι_app],
end

@[ext] lemma free.ext {X : C} {A : endomorphisms C} (f g : free X ⟶ A)
  (w : sigma.ι (λ i : ulift.{v} ℕ, X) ⟨0⟩ ≫ f.f = sigma.ι (λ i : ulift.{v} ℕ, X) ⟨0⟩ ≫ g.f) :
  f = g :=
begin
  ext ⟨i⟩, dsimp,
  induction i with i ih, { exact w },
  apply_fun (λ α, α ≫ A.e) at ih,
  simp only [category.assoc, ← hom.comm, free.ι_comp_e_assoc] at ih,
  exact ih,
end

/-- The map `free T ⟶ A` in `endomorphisms C` induced by a map `T ⟶ A.X` in `C`. Here `A.X`
is the forgetful functor forgetting the endomorphism. -/
@[simps]
def free.desc {X : C} {A : endomorphisms C} (f : X ⟶ A.X) : free X ⟶ A :=
{ f := sigma.desc $ λ i, f ≫ (A.e ^ i.down : End A.X),
  comm := begin
    ext1 ⟨i⟩, dsimp,
    simp only [colimit.ι_desc_assoc, cofan.mk_ι_app,
      colimit.ι_desc, category.assoc, pow_succ, End.mul_def],
  end }

lemma free.desc_comp {X : C} {A B : endomorphisms C} (f : X ⟶ A.X) (g : A ⟶ B) :
  free.desc f ≫ g = free.desc (f ≫ g.f) :=
begin
  ext1, dsimp,
  simp only [colimit.ι_desc_assoc, cofan.mk_ι_app, colimit.ι_desc, category.assoc, pow_comm],
end

def free.map {X Y : C} (f : X ⟶ Y) : free X ⟶ free Y :=
{ f := sigma.desc $ λ i, f ≫ sigma.ι (λ i : ulift.{v} ℕ, Y) i,
  comm := begin
    ext1 ⟨i⟩,
    dsimp,
    simp only [colimit.ι_desc_assoc, cofan.mk_ι_app, colimit.ι_desc, category.assoc],
  end }

variable (C)

def functor.free : C ⥤ endomorphisms C :=
{ obj := free,
  map := λ _ _, free.map,
  map_id' := λ X, begin ext, dsimp, simp only [free.map, category.id_comp, colimit.ι_desc,
    cofan.mk_ι_app, category.comp_id], end,
  map_comp' := λ X Y Z f g, begin ext, dsimp, simp only [free.map, category.assoc, colimit.ι_desc,
    cofan.mk_ι_app, colimit.ι_desc_assoc], end }

end free

section cofree

variable {C}
variable [has_products_of_shape (ulift.{v} ℕ) C]

/-- `cofree X` is ∏ₙX, the product over the naturals, equipped with the endomorphism
sending `(a : X)` in degree `n` to `a` in degree `n+1`. -/
def cofree (X : C) : endomorphisms C :=
{ X := ∏ (λ i : ulift.{v} ℕ, X),
  e := pi.lift $ λ i, pi.π _ ⟨i.down + 1⟩ }

def cofree.lift {X : C} {A : endomorphisms C} (f : A.X ⟶ X) :
  A ⟶ cofree X :=
{ f := pi.lift $ λ i, (A.e ^ i.down : End A.X) ≫ f,
  comm := begin
    dsimp [cofree],
    ext ⟨j⟩, dsimp,
    simp only [category.assoc, limit.lift_π, fan.mk_π_app],
    rw [← category.assoc, pow_succ, ← End.mul_def], congr' 1,
    induction j with j hj,
    { simp },
    { simp only [End.mul_def, pow_succ] at *,
      simp [reassoc_of hj] }
  end }

end cofree

variables [has_products_of_shape (ulift.{v} ℕ) C] [has_coproducts_of_shape (ulift.{v} ℕ) C]

lemma f_epi {X Y : endomorphisms C} (f : X ⟶ Y) [epi f] : epi f.f :=
{ left_cancellation := λ Z g h w, begin
    let gg : Y ⟶ cofree Z := cofree.lift g,
    let hh : Y ⟶ cofree Z := cofree.lift h,
    have : f ≫ gg = f ≫ hh,
    { ext, dsimp [gg, hh, cofree.lift], simp,
      simp_rw [← category.assoc, ← pow_comm, category.assoc, w] },
    rw cancel_epi at this,
    apply_fun (λ e, e.f ≫ pi.π (λ i : ulift.{v} ℕ, Z) (ulift.up 0)) at this,
    dsimp [gg, hh, cofree.lift] at this, simpa using this,
  end }

lemma f_mono {X Y : endomorphisms C} (f : X ⟶ Y) [mono f] : mono f.f :=
{ right_cancellation := λ Z g h w, begin
    let gg : free Z ⟶ X := free.desc g,
    let hh : free Z ⟶ X := free.desc h,
    have : gg ≫ f = hh ≫ f,
    { ext, dsimp [gg,hh, free.desc], simpa },
    rw cancel_mono at this,
    apply_fun (λ e, sigma.ι ((λ i : ulift.{v} ℕ, Z)) (ulift.up 0) ≫ e.f) at this,
    dsimp [gg, hh, free.desc] at this, simpa using this
  end }

instance free.projective (X : C) [projective X] : projective (free X) :=
{ factors := λ E Y f e he, begin
    resetI,
    let φ : X ⟶ Y.X := sigma.ι (λ i : ulift.{v} ℕ, X) ⟨0⟩ ≫ f.f,
    haveI : epi e.f := f_epi _,
    use free.desc (projective.factor_thru φ e.f),
    rw [free.desc_comp, projective.factor_thru_comp],
    ext1, dsimp, simp only [colimit.ι_desc, cofan.mk_ι_app, pow_zero, End.one_def, category.comp_id],
  end }

def free.presentation [enough_projectives C] (A : endomorphisms C) :
  projective_presentation A :=
{ P := free (projective.over A.X),
  projective := infer_instance,
  f := free.desc $ projective.π _,
  epi := begin
    suffices : epi (free.desc (projective.π A.X)).f,
    { resetI, apply epi_of_epi_f },
    dsimp,
    refine @epi_of_epi _ _ _ _ _ (sigma.ι _ _) _ (id _), { exact ⟨0⟩ },
    simp only [colimit.ι_desc, cofan.mk_ι_app, pow_zero, End.one_def, category.comp_id],
    apply_instance
  end }

instance [enough_projectives C] : enough_projectives (endomorphisms C) :=
{ presentation := λ A, ⟨free.presentation A⟩ }

-- generalize to colimits
instance projective_sigma {C ι : Type*} [category C] (P : ι → C) [has_coproduct P]
  [∀ i, projective (P i)] :
  projective (∐ P) :=
{ factors := begin
  introsI E X f e he,
  let φ : ∐ P ⟶ E := sigma.desc (λ i, projective.factor_thru (sigma.ι _ _ ≫ f) e),
  refine ⟨φ, _⟩,
  ext i,
  rw [limits.colimit.ι_desc_assoc, limits.cofan.mk_ι_app, projective.factor_thru_comp],
end }

instance projective_X [enough_projectives C] (P : endomorphisms C) [projective P] :
  projective P.X :=
⟨λ E X f e he, begin
  let F := free.presentation P,
  haveI : projective F.P.X := endomorphisms.projective_sigma _,
  haveI : epi F.f := F.epi,
  let s : P ⟶ F.P := projective.factor_thru (𝟙 _) F.f,
  have hsπ : s ≫ F.f = 𝟙 _ := projective.factor_thru_comp _ _,
  let X' : endomorphisms C := ⟨X, 𝟙 _⟩,
  let E' : endomorphisms C := ⟨E, 𝟙 _⟩,
  let e' : E' ⟶ X' := ⟨e, by { dsimp only, rw [category.id_comp, category.comp_id] }⟩,
  haveI he' : epi e' := epi_of_epi_f e',
  let φ : F.P.X ⟶ E := projective.factor_thru (F.f.f ≫ f) e,
  refine ⟨s.f ≫ φ, _⟩,
  rw [category.assoc, projective.factor_thru_comp, ← comp_f_assoc, hsπ, id_f, category.id_comp],
end⟩

end projectives

section preadditive
open category_theory.preadditive

variables {𝓐 : Type u} [category.{v} 𝓐] [preadditive 𝓐]
variables (X Y : endomorphisms 𝓐)

instance : has_zero (X ⟶ Y) := ⟨⟨0, by simp only [comp_zero, zero_comp, hom.comm]⟩⟩
instance : has_add (X ⟶ Y) := ⟨λ f g, ⟨f.f + g.f, by simp only [comp_add, add_comp, hom.comm]⟩⟩
instance : has_sub (X ⟶ Y) := ⟨λ f g, ⟨f.f - g.f, by simp only [comp_sub, sub_comp, hom.comm]⟩⟩
instance : has_neg (X ⟶ Y) := ⟨λ f, ⟨-f.f, by simp only [comp_neg, neg_comp, hom.comm]⟩⟩
instance has_nsmul : has_scalar ℕ (X ⟶ Y) := ⟨λ n f, ⟨n • f.f, by simp only [comp_nsmul, nsmul_comp, hom.comm]⟩⟩
instance has_zsmul : has_scalar ℤ (X ⟶ Y) := ⟨λ n f, ⟨n • f.f, by simp only [comp_zsmul, zsmul_comp, hom.comm]⟩⟩

instance : add_comm_group (X ⟶ Y) :=
(f_injective X Y).add_comm_group _ rfl (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl)

@[simp] lemma zero_f : hom.f (0 : X ⟶ Y) = 0 := rfl
variables {X Y} (f g : X ⟶ Y)
@[simp] lemma add_f : (f + g).f = f.f + g.f := rfl
@[simp] lemma sub_f : (f - g).f = f.f - g.f := rfl
@[simp] lemma neg_f : (-f).f = -(f.f) := rfl
@[simp] lemma nsmul_f (n : ℕ) (f : X ⟶ Y) : (n • f).f = n • f.f := rfl
@[simp] lemma zsmul_f (n : ℤ) (f : X ⟶ Y) : (n • f).f = n • f.f := rfl

variables (𝓐)

instance : preadditive (endomorphisms 𝓐) :=
{ add_comp' := by { intros, ext, dsimp, rw add_comp },
  comp_add' := by { intros, ext, dsimp, rw comp_add } }

instance forget_additive : (endomorphisms.forget 𝓐).additive := {}

instance functor.free_additive [has_coproducts_of_shape (ulift.{v} ℕ) 𝓐] :
  (functor.free 𝓐).additive := ⟨λ X Y f g, by { delta functor.free free.map,
    ext, simp, }⟩

lemma is_zero_X {X : endomorphisms 𝓐} (h : is_zero X) : is_zero X.X :=
by { rw is_zero_iff_id_eq_zero at h ⊢, apply_fun (λ a, a.f) at h, exact h }

end preadditive

section abelian

variables {𝓐 : Type u} [category.{v} 𝓐] [abelian 𝓐]
  {X Y : endomorphisms 𝓐} (f : X ⟶ Y)

@[simps]
protected def kernel_obj : endomorphisms 𝓐 :=
{ X := kernel f.f,
  e := kernel.lift _ (kernel.ι _ ≫ X.e) (by simp) }

@[simps]
protected def kernel_ι : endomorphisms.kernel_obj f ⟶ X :=
{ f := kernel.ι _,
  comm := by { dsimp, simp } }

protected def kernel_fork : kernel_fork f :=
kernel_fork.of_ι (endomorphisms.kernel_ι f) $ by { ext, dsimp, simp }

@[simp]
protected lemma kernel_fork_ι_f :
  (endomorphisms.kernel_fork f).ι.f = kernel.ι _ := rfl

@[simps]
protected def kernel_lift (s : kernel_fork f) :
  s.X ⟶ endomorphisms.kernel_obj f :=
{ f := kernel.lift _ s.ι.f $ by { rw [← comp_f, s.condition, zero_f], },
  comm := by { ext, dsimp, simp } }

@[simps]
protected def is_limit_kernel_fork : is_limit (endomorphisms.kernel_fork f) :=
is_limit_aux _
(λ s, endomorphisms.kernel_lift f s)
(λ s, by { ext, dsimp, simp })
(λ s m hm, by { apply_fun (λ e, e.f) at hm, ext, dsimp at *, simp [hm] } )

instance has_kernels : has_kernels (endomorphisms 𝓐) :=
⟨λ X Y f, ⟨⟨⟨endomorphisms.kernel_fork _, endomorphisms.is_limit_kernel_fork _⟩⟩⟩⟩

@[simps]
protected def cokernel_obj : endomorphisms 𝓐 :=
{ X := cokernel f.f,
  e := cokernel.desc _ (Y.e ≫ cokernel.π _) $
    by { simp only [← (reassoc_of f.comm), cokernel.condition, comp_zero] } }

@[simps]
protected def cokernel_π : Y ⟶ endomorphisms.cokernel_obj f :=
{ f := cokernel.π _,
  comm := by simp }

protected def cokernel_cofork : cokernel_cofork f :=
cokernel_cofork.of_π (endomorphisms.cokernel_π f) $ by { ext, dsimp, simp }

@[simp]
protected lemma cokernel_cofork_π_f :
  (endomorphisms.cokernel_cofork f).π.f = cokernel.π _ := rfl

@[simps]
protected def cokernel_desc (s : cokernel_cofork f) :
  endomorphisms.cokernel_obj f ⟶ s.X :=
{ f := cokernel.desc _ s.π.f $ by { rw [← comp_f, s.condition, zero_f] },
  comm := by { ext, dsimp, simp } }

@[simps]
protected def is_colimit_cokernel_cofork : is_colimit (endomorphisms.cokernel_cofork f) :=
is_colimit_aux _
(λ s, endomorphisms.cokernel_desc f s)
(λ s, by { ext, dsimp, simp })
(λ s m hm, by { apply_fun (λ e, e.f) at hm, ext, dsimp at *, simp [hm] })

instance has_cokernels : has_cokernels (endomorphisms 𝓐) :=
⟨λ X Y f, ⟨⟨⟨endomorphisms.cokernel_cofork _, endomorphisms.is_colimit_cokernel_cofork _⟩⟩⟩⟩

def kernel_fork_iso :
  endomorphisms.kernel_fork f ≅ kernel_fork.of_ι (endomorphisms.kernel_ι f)
  (endomorphisms.kernel_fork f).condition :=
cones.ext
(iso.refl _)
(by { rintro (_|_); tidy })

def is_limit_fork_of_is_limit
  (hF : is_limit (limits.kernel_fork.of_ι f.f (cokernel.condition _))) :
  is_limit (limits.kernel_fork.of_ι f (endomorphisms.cokernel_cofork _).condition) :=
is_limit_aux _
(λ S,
{ f := hF.lift (kernel_fork.of_ι S.ι.f begin
    change _ ≫ (endomorphisms.cokernel_cofork _).π.f = _,
    erw [← comp_f, S.condition, zero_f],
  end),
  comm := begin
    apply hF.hom_ext, rintro (_|_),
    { dsimp, simp only [category.assoc, hom.comm], erw hF.fac _ (walking_parallel_pair.zero),
      erw hF.fac_assoc _ (walking_parallel_pair.zero),
      dsimp, simp, },
    { dsimp, simp, }
  end })
begin
  intros S,
  ext, dsimp, erw hF.fac _ walking_parallel_pair.zero, refl,
end
begin
  intros S m hm,
  ext, dsimp, apply hF.hom_ext, rintros (_|_),
  { apply_fun (λ e, e.f) at hm,
    dsimp at *,
    simp only [hm],
    erw hF.fac _ (walking_parallel_pair.zero), refl },
  { dsimp, simp },
end

def is_colimit_cofork_of_is_colimit
  (hF : is_colimit (limits.cokernel_cofork.of_π f.f (kernel.condition _))) :
  is_colimit (limits.cokernel_cofork.of_π f (endomorphisms.kernel_fork _).condition) :=
is_colimit_aux _
(λ S,
{ f := hF.desc (cokernel_cofork.of_π S.π.f begin
    change (endomorphisms.kernel_fork _).ι.f ≫ _ = _,
    erw [← comp_f, S.condition, zero_f]
  end),
  comm := begin
    apply hF.hom_ext, rintro (_|_),
    { dsimp, simp },
    { dsimp, erw hF.fac_assoc _ (walking_parallel_pair.one),
      rw [← hom.comm_assoc],
      erw hF.fac _ (walking_parallel_pair.one),
      dsimp, simp }
  end })
begin
  intros S,
  ext, dsimp, erw hF.fac _ walking_parallel_pair.one, refl,
end
begin
  intros S m hm,
  ext, dsimp, apply hF.hom_ext, rintros (_|_),
  { dsimp, simp },
  { apply_fun (λ e, e.f) at hm,
    dsimp at *,
    simp only [hm],
    erw hF.fac _ walking_parallel_pair.one, refl }
end

instance [has_coproducts_of_shape (ulift.{v} ℕ) 𝓐] [has_products_of_shape (ulift.{v} ℕ) 𝓐] :
  abelian (endomorphisms 𝓐) :=
{ normal_mono_of_mono := begin
    introsI X Y f _,
    haveI := f_mono f,
    let hE : is_limit (kernel_fork.of_ι f.f _) :=
      category_theory.abelian.mono_is_kernel_of_cokernel _ (colimit.is_colimit _),
    fconstructor,
    exact endomorphisms.cokernel_obj f,
    exact endomorphisms.cokernel_π f,
    exact (endomorphisms.cokernel_cofork f).condition,
    apply is_limit_fork_of_is_limit _ hE,
  end,
  normal_epi_of_epi := begin
    introsI X Y f _,
    haveI := f_epi f,
    let hE : is_colimit (cokernel_cofork.of_π f.f _) :=
      category_theory.abelian.epi_is_cokernel_of_kernel _ (limit.is_limit _),
    fconstructor,
    exact endomorphisms.kernel_obj f,
    exact endomorphisms.kernel_ι f,
    exact (endomorphisms.kernel_fork f).condition,
    apply is_colimit_cofork_of_is_colimit _ hE,
  end,
  has_finite_products := begin
    constructor, intros J _ _,
    haveI : has_finite_products 𝓐 := abelian.has_finite_products, -- WHY IS THIS NEEDED!?
    apply_instance,
  end,
  .. (_ : preadditive (endomorphisms 𝓐)) }

end abelian

end endomorphisms

end category_theory
