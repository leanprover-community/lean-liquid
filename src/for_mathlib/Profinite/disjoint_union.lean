import topology.category.Profinite
import category_theory.limits.shapes.products

/-!

In this file we show that a finite disjoint union of profinite sets agrees with the coproduct.
*Note:* The existence of the coproduct is currently shown using some abstract nonsense.

-/

namespace topology

instance {α : Type*} [fintype α] (X : α → Type*) [∀ a, topological_space (X a)]
  [∀ a, compact_space (X a)] : compact_space (Σ a, X a) := sorry

instance {α : Type*} [fintype α] (X : α → Type*) [∀ a, topological_space (X a)]
  [∀ a, totally_disconnected_space (X a)] : totally_disconnected_space (Σ a, X a) := sorry

end topology

namespace Profinite

universe u
variables {α : Type u} [fintype α] (X : α → Profinite.{u})

def empty : Profinite := Profinite.of pempty
def empty.elim (X : Profinite) : empty ⟶ X :=  { to_fun := pempty.elim }

def sigma : Profinite :=
Profinite.of $ Σ a, X a

def sigma.ι (a : α) : X a ⟶ sigma X :=
{ to_fun := λ t, ⟨_,t⟩,
  continuous_to_fun := sorry }

lemma sigma.ι_injective (a : α) : function.injective (sigma.ι X a) :=
by { dsimp [sigma.ι], exact sigma_mk_injective }

lemma sigma.ι_jointly_surjective (t : sigma X) : ∃ a (x : X a), sigma.ι X a x = t :=
by { rcases t with ⟨a,t⟩, exact ⟨a,t,rfl⟩ }

def sigma.desc {Y} (f : Π a, X a ⟶ Y) : sigma X ⟶ Y :=
{ to_fun := λ ⟨a,t⟩, f a t,
  continuous_to_fun := sorry }

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
open category_theory.limits

def sigma_cofan : cofan X :=
cofan.mk (sigma X) (sigma.ι X)

def sigma_cofan_is_colimit : is_colimit (sigma_cofan X) :=
{ desc := λ S, sigma.desc _ $ λ a, S.ι.app a,
  uniq' := begin
    intros S m h,
    apply sigma.hom_ext,
    intros a,
    convert h a,
    simp,
  end }

def explicit_pullback {X Y B : Profinite} (f : X ⟶ B) (g : Y ⟶ B) : Profinite :=
{ to_CompHaus :=
  { to_Top := Top.of { a : X × Y | f a.1 = g a.2 },
    is_compact := sorry,
    is_hausdorff := sorry },
  is_totally_disconnected := sorry }

def explicit_pullback.fst {X Y B : Profinite} (f : X ⟶ B) (g : Y ⟶ B) :
  explicit_pullback f g ⟶ X := { to_fun := λ a, a.1.1 }

def explicit_pullback.snd {X Y B : Profinite} (f : X ⟶ B) (g : Y ⟶ B) :
  explicit_pullback f g ⟶ Y := { to_fun := λ a, a.1.2 }

lemma explicit_pullback.condition {X Y B : Profinite} (f : X ⟶ B) (g : Y ⟶ B) :
  explicit_pullback.fst f g ≫ f = explicit_pullback.snd f g ≫ g := by { ext ⟨t,ht⟩, exact ht }

def explicit_pullback.lift {W X Y B : Profinite} (f : X ⟶ B) (g : Y ⟶ B)
  (e₁ : W ⟶ X) (e₂ : W ⟶ Y) (w : e₁ ≫ f = e₂ ≫ g) : W ⟶ explicit_pullback f g :=
{ to_fun := λ t, ⟨(e₁ t, e₂ t), by { apply_fun (λ ee, ee t) at w, exact w }⟩ }

--TODO: Finish off the api for the explicit pullback

end Profinite
