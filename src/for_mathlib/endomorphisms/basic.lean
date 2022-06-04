import category_theory.abelian.projective

noncomputable theory

universes v u

open category_theory category_theory.limits

namespace category_theory

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

@[simp] lemma comp_f {X Y Z : endomorphisms C} (f : X ⟶ Y) (g : Y ⟶ Z) :
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

protected def forget (C : Type u) [category.{v} C] : endomorphisms C ⥤ C :=
{ obj := λ X, X.X,
  map := λ X Y f, f.f,
  map_id' := λ X, rfl,
  map_comp' := λ X Y Z f g, rfl }

lemma epi_of_epi_f {X Y : endomorphisms C} (f : X ⟶ Y) [epi f.f] : epi f :=
{ left_cancellation := λ Z g h w, begin
    ext, rw [← cancel_epi f.f, ← comp_f, w, comp_f],
  end }

end category

section projectives

variables {C : Type u} [category.{v} C] [has_coproducts_of_shape (ulift.{v} ℕ) C]
  [has_products_of_shape (ulift.{v} ℕ) C]

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

end preadditive

section abelian

variables (𝓐 : Type u) [category.{v} 𝓐]

instance [abelian 𝓐] : abelian (endomorphisms 𝓐) :=
{ normal_mono_of_mono := sorry,
  normal_epi_of_epi := sorry,
  has_finite_products := sorry,
  has_kernels := sorry,
  has_cokernels := sorry,
  .. (_ : preadditive (endomorphisms 𝓐)) }

end abelian

end endomorphisms

end category_theory
