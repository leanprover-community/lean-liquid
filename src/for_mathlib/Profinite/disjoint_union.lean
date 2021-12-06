import category_theory.limits.shapes.products
import for_mathlib.Profinite.compat_discrete_quotient
import topology.category.Profinite

/-!

In this file we show that a finite disjoint union of profinite sets agrees with the coproduct.
*Note:* The existence of the coproduct is currently shown using some abstract nonsense.

-/

namespace Profinite

universe u
variables {α : Type u} [fintype α] (X : α → Profinite.{u})

def empty : Profinite.{u} := Profinite.of pempty
def empty.elim (X : Profinite.{u}) : empty ⟶ X :=  { to_fun := pempty.elim }

def sum (X Y : Profinite.{u}) : Profinite.{u} :=
Profinite.of $ X ⊕ Y

def sum.inl (X Y : Profinite.{u}) : X ⟶ sum X Y :=
{ to_fun := _root_.sum.inl }

def sum.inr (X Y : Profinite.{u}) : Y ⟶ sum X Y :=
{ to_fun := _root_.sum.inr }

def sum.desc {Z} (X Y : Profinite.{u}) (f : X ⟶ Z) (g : Y ⟶ Z) : sum X Y ⟶ Z :=
{ to_fun := λ x, _root_.sum.rec_on x f g,
  continuous_to_fun := begin
    apply continuous_sup_dom,
    { apply continuous_coinduced_dom, exact f.continuous },
    { apply continuous_coinduced_dom, exact g.continuous }
  end }

@[simp]
lemma sum.inl_desc {Z} (X Y : Profinite.{u}) (f : X ⟶ Z) (g : Y ⟶ Z) :
  sum.inl X Y ≫ sum.desc X Y f g = f := by { ext, refl }

@[simp]
lemma sum.inr_desc {Z} (X Y : Profinite.{u}) (f : X ⟶ Z) (g : Y ⟶ Z) :
  sum.inr X Y ≫ sum.desc X Y f g = g := by { ext, refl }

lemma sum.hom_ext {Z} (X Y : Profinite.{u}) (e₁ e₂ : sum X Y ⟶ Z)
  (hl : sum.inl X Y ≫ e₁ = sum.inl X Y ≫ e₂) (hr : sum.inr X Y ≫ e₁ = sum.inr X Y ≫ e₂) :
  e₁ = e₂ :=
begin
  ext (u|u),
  { apply_fun (λ e, e u) at hl, exact hl },
  { apply_fun (λ e, e u) at hr, exact hr },
end

def sigma : Profinite.{u} :=
Profinite.of $ Σ a, X a

def sigma.ι (a : α) : X a ⟶ sigma X :=
{ to_fun := λ t, ⟨_,t⟩,
  continuous_to_fun := begin
    apply continuous_Sup_rng,
    exact ⟨a,rfl⟩,
    apply continuous_coinduced_rng,
  end }

lemma sigma.ι_injective (a : α) : function.injective (sigma.ι X a) :=
by { dsimp [sigma.ι], exact sigma_mk_injective }

lemma sigma.ι_jointly_surjective (t : sigma X) : ∃ a (x : X a), sigma.ι X a x = t :=
by { rcases t with ⟨a,t⟩, exact ⟨a,t,rfl⟩ }

def sigma.desc {Y} (f : Π a, X a ⟶ Y) : sigma X ⟶ Y :=
{ to_fun := λ ⟨a,t⟩, f a t,
  continuous_to_fun := begin
    apply continuous_Sup_dom,
    rintros _ ⟨a,rfl⟩,
    resetI,
    apply continuous_coinduced_dom,
    exact (f a).continuous
  end }

lemma sigma.desc_surjective {Y} (f : Π a, X a ⟶ Y) (surj : ∀ y, ∃ a (x : X a), f a x = y) :
  function.surjective (sigma.desc X f) :=
begin
  intros y,
  obtain ⟨a,x,hx⟩ := surj y,
  exact ⟨⟨a,x⟩,hx⟩,
end

@[simp, reassoc]
lemma sigma.ι_desc {Y} (a) (f : Π a, X a ⟶ Y) : sigma.ι X a ≫ sigma.desc X f = f a :=
by { ext, refl }

lemma sigma.hom_ext {Y} (f g : sigma X ⟶ Y) (w : ∀ a, sigma.ι X a ≫ f = sigma.ι X a ≫ g) :
  f = g :=
begin
  ext ⟨a,t⟩,
  specialize w a,
  apply_fun (λ e, e t) at w,
  exact w,
end

open category_theory

def sigma_cofan : limits.cofan X :=
limits.cofan.mk (sigma X) (sigma.ι X)

def sigma_cofan_is_colimit : limits.is_colimit (sigma_cofan X) :=
{ desc := λ S, sigma.desc _ $ λ a, S.ι.app a,
  uniq' := begin
    intros S m h,
    apply sigma.hom_ext,
    intros a,
    convert h a,
    simp,
  end }

def pullback {X Y B : Profinite.{u}} (f : X ⟶ B) (g : Y ⟶ B) : Profinite :=
{ to_CompHaus :=
  { to_Top := Top.of { a : X × Y | f a.1 = g a.2 },
    is_compact := begin
      erw ← is_compact_iff_compact_space,
      apply is_closed.is_compact,
      apply is_closed_eq,
      all_goals { continuity },
    end,
    is_hausdorff := begin
      change t2_space { a : X × Y | f a.1 = g a.2 },
      apply_instance
    end },
  is_totally_disconnected := subtype.totally_disconnected_space }

def pullback.fst {X Y B : Profinite.{u}} (f : X ⟶ B) (g : Y ⟶ B) :
  pullback f g ⟶ X := { to_fun := λ a, a.1.1 }

def pullback.snd {X Y B : Profinite.{u}} (f : X ⟶ B) (g : Y ⟶ B) :
  pullback f g ⟶ Y := { to_fun := λ a, a.1.2 }

lemma pullback.condition {X Y B : Profinite.{u}} (f : X ⟶ B) (g : Y ⟶ B) :
  pullback.fst f g ≫ f = pullback.snd f g ≫ g := by { ext ⟨t,ht⟩, exact ht }

def pullback.lift {W X Y B : Profinite.{u}} (f : X ⟶ B) (g : Y ⟶ B)
  (e₁ : W ⟶ X) (e₂ : W ⟶ Y) (w : e₁ ≫ f = e₂ ≫ g) : W ⟶ pullback f g :=
{ to_fun := λ t, ⟨(e₁ t, e₂ t), by { apply_fun (λ ee, ee t) at w, exact w }⟩ }

@[simp, reassoc]
lemma pullback.lift_fst {W X Y B : Profinite.{u}} (f : X ⟶ B) (g : Y ⟶ B)
  (e₁ : W ⟶ X) (e₂ : W ⟶ Y) (w : e₁ ≫ f = e₂ ≫ g) :
  pullback.lift f g e₁ e₂ w ≫ pullback.fst f g = e₁ := by { ext, refl }

@[simp, reassoc]
lemma pullback.lift_snd {W X Y B : Profinite.{u}} (f : X ⟶ B) (g : Y ⟶ B)
  (e₁ : W ⟶ X) (e₂ : W ⟶ Y) (w : e₁ ≫ f = e₂ ≫ g) :
  pullback.lift f g e₁ e₂ w ≫ pullback.snd f g = e₂ := by { ext, refl }

lemma pullback.hom_ext {W X Y B : Profinite.{u}} (f : X ⟶ B) (g : Y ⟶ B) (e₁ e₂ : W ⟶ pullback f g)
  (w₁ : e₁ ≫ pullback.fst f g = e₂ ≫ pullback.fst f g)
  (w₂ : e₁ ≫ pullback.snd f g = e₂ ≫ pullback.snd f g) : e₁ = e₂ :=
begin
  ext t,
  { apply_fun (λ e, e t) at w₁, exact w₁ },
  { apply_fun (λ e, e t) at w₂, exact w₂ },
end

def sigma_pullback_to_pullback_sigma {B} (f : Π a, X a ⟶ B) :
  sigma (λ a : α × α, pullback (f a.1) (f a.2)) ⟶ pullback (sigma.desc X f) (sigma.desc X f) :=
sigma.desc _ $ λ a, pullback.lift _ _
  (pullback.fst _ _ ≫ sigma.ι _ _) (pullback.snd _ _ ≫ sigma.ι _ _) begin
    cases a, dsimp at *, ext1, cases x, assumption,
  end

instance {B} (f : Π a, X a ⟶ B) : is_iso (sigma_pullback_to_pullback_sigma X f) :=
is_iso_of_bijective _
begin
  split,
  { rintros ⟨⟨a,b⟩,⟨⟨x₁,x₂⟩,hx⟩⟩ ⟨⟨a',b'⟩,⟨⟨x'₁,x'₂⟩,hx'⟩⟩ h,
    dsimp [sigma_pullback_to_pullback_sigma, sigma.desc, pullback.lift,
      sigma.ι, pullback.fst, pullback.snd] at *,
    tidy },
  { rintros ⟨⟨⟨a,x⟩,⟨b,y⟩⟩,h⟩,
    refine ⟨⟨⟨a,b⟩,⟨⟨x,y⟩,h⟩⟩,rfl⟩ }
end

@[simp]
lemma sigma_pullback_to_pullback_sigma_fst {B} (f : Π a, X a ⟶ B) :
  sigma_pullback_to_pullback_sigma X f ≫ pullback.fst _ _ =
  sigma.desc _ (λ a, pullback.fst _ _ ≫ sigma.ι _ a.1) := by ext ⟨_,_⟩; refl

@[simp]
lemma sigma_pullback_to_pullback_sigma_snd {B} (f : Π a, X a ⟶ B) :
  sigma_pullback_to_pullback_sigma X f ≫ pullback.snd _ _ =
  sigma.desc _ (λ a, pullback.snd _ _ ≫ sigma.ι _ a.2) := by ext ⟨_,_⟩; refl

--TODO: Finish off the api for the explicit pullback

def equalizer {X Y : Profinite.{u}} (f g : X ⟶ Y) : Profinite :=
{ to_CompHaus :=
  { to_Top := Top.of { x | f x = g x },
    is_compact := begin
      erw ← is_compact_iff_compact_space,
      apply is_closed.is_compact,
      apply is_closed_eq,
      exact f.continuous,
      exact g.continuous
    end,
    is_hausdorff := begin
      change t2_space { x | f x = g x },
      apply_instance
    end },
  is_totally_disconnected := subtype.totally_disconnected_space }

def equalizer.ι {X Y : Profinite.{u}} (f g : X ⟶ Y) : equalizer f g ⟶ X := { to_fun := λ x, x.1 }

def equalizer.lift {W X Y : Profinite.{u}} (f g : X ⟶ Y) (e : W ⟶ X) (w : e ≫ f = e ≫ g) :
  W ⟶ equalizer f g :=
{ to_fun := λ t, ⟨e t, by { apply_fun (λ ee, ee t) at w, exact w }⟩ }

@[simp, reassoc]
lemma equalizer.lift_ι {W X Y : Profinite.{u}} (f g : X ⟶ Y) (e : W ⟶ X)
  (w : e ≫ f = e ≫ g) : equalizer.lift f g e w ≫ equalizer.ι f g = e := by { ext, refl }

lemma equalizer.hom_ext {W X Y : Profinite.{u}} (f g : X ⟶ Y) (e₁ e₂ : W ⟶ equalizer f g)
  (w : e₁ ≫ equalizer.ι f g = e₂ ≫ equalizer.ι f g) : e₁ = e₂ :=
begin
  ext t,
  apply_fun (λ ee, ee t) at w,
  exact w,
end

/-- Descend a morphism along a surjective morphism. -/
noncomputable
def descend {X B Y : Profinite} (π : X ⟶ B) (t : X ⟶ Y) (hπ : function.surjective π)
  (w : pullback.fst π π ≫ t = pullback.snd π π ≫ t) : B ⟶ Y :=
{ to_fun := let e := setoid.quotient_ker_equiv_of_surjective _ hπ in
    (λ (i : quotient (setoid.ker π)), quotient.lift_on' i t begin
      rintros a b (h : π _ = π _),
      let c : Profinite.pullback π π := ⟨(a,b),h⟩,
      apply_fun (λ e, e c) at w,
      exact w,
    end) ∘ e.symm,
  continuous_to_fun := begin
    -- This should follow from the following...
    have := discrete_quotient.quotient_map π hπ, -- TODO: This is in the wrong namespace :-/
    sorry,
  end }

@[simp]
lemma π_descend {X B Y : Profinite} (π : X ⟶ B) (t : X ⟶ Y) (hπ : function.surjective π)
  (w : pullback.fst π π ≫ t = pullback.snd π π ≫ t) :
  π ≫ descend π t hπ w = t :=
begin
  ext i,
  dsimp [descend, setoid.quotient_ker_equiv_of_surjective,
    setoid.quotient_ker_equiv_of_right_inverse],
  let c : pullback π π := ⟨(function.surj_inv hπ (π i), i), function.surj_inv_eq hπ (π i)⟩,
  apply_fun (λ e, e c) at w,
  exact w,
end

end Profinite
