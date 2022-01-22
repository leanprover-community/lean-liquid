-- From AT: This approach could work, but seems too complicated for now.
-- I have opted to use the comparison lemma instead.
/-
import topology.category.Profinite
import for_mathlib.Profinite.disjoint_union

open category_theory

namespace Profinite

universe u

/- The following three lemmas are used below to help speed up some proofs. -/

@[simp] lemma pullback.fst_apply {A B C : Profinite.{u}} (f : A ⟶ C) (g : B ⟶ C)
  (a : A) (b : B) (h : f a = g b) : Profinite.pullback.fst f g ⟨(a,b),h⟩ = a := rfl

@[simp] lemma pullback.snd_apply {A B C : Profinite.{u}} (f : A ⟶ C) (g : B ⟶ C)
  (a : A) (b : B) (h : f a = g b) : Profinite.pullback.snd f g ⟨(a,b),h⟩ = b := rfl

@[simp] lemma pullback.lift_apply {A B C D : Profinite.{u}} (f : A ⟶ C) (g : B ⟶ C)
  (a : D ⟶ A) (b : D ⟶ B) (w : a ≫ f = b ≫ g) (d : D) :
  Profinite.pullback.lift f g a b w d = ⟨(a d, b d), by { change (a ≫ f) d = _, rw w, refl }⟩ :=
rfl

structure prepresentation (B : Profinite.{u}) :=
(G : Profinite.{u})
(π : G ⟶ B)
(hπ : function.surjective π)
(R : Profinite.{u})
(r : R ⟶ Profinite.pullback π π)
(hr : function.surjective r)

def prepresentation.fst {B : Profinite.{u}} (P : B.prepresentation) :
  P.R ⟶ P.G :=
P.r ≫ Profinite.pullback.fst _ _

def prepresentation.snd {B : Profinite.{u}} (P : B.prepresentation) :
  P.R ⟶ P.G :=
P.r ≫ Profinite.pullback.snd _ _

lemma prepresentation.fst_surjective {B : Profinite.{u}} (P : B.prepresentation) :
  function.surjective P.fst :=
begin
  apply function.surjective.comp _ P.hr,
  intros x,
  exact ⟨⟨⟨x,x⟩,rfl⟩,rfl⟩,
end

lemma prepresentation.snd_surjective {B : Profinite.{u}} (P : B.prepresentation) :
  function.surjective P.snd :=
begin
  apply function.surjective.comp _ P.hr,
  intros x,
  exact ⟨⟨⟨x,x⟩,rfl⟩,rfl⟩,
end

def prepresentation.base {B : Profinite.{u}} (P : B.prepresentation) :
  P.R ⟶ B :=
P.snd ≫ P.π

@[simp, reassoc, elementwise]
lemma prepresentation.base_fst {B : Profinite.{u}} (P : B.prepresentation) :
  P.fst ≫ P.π = P.base :=
by { dsimp [prepresentation.fst, prepresentation.snd, prepresentation.base],
  simp [Profinite.pullback.condition] }

@[simp, reassoc, elementwise]
lemma prepresentation.base_snd {B : Profinite.{u}} (P : B.prepresentation) :
  P.snd ≫ P.π = P.base := rfl

lemma prepresentation.base_surjective {B : Profinite.{u}} (P : B.prepresentation) :
  function.surjective P.base := function.surjective.comp P.hπ P.snd_surjective

structure prepresentation.hom_over {B₁ B₂ : Profinite.{u}}
  (X₁ : B₁.prepresentation) (X₂ : B₂.prepresentation) (f : B₁ ⟶ B₂) :=
(g : X₁.G ⟶ X₂.G)
(hg : g ≫ X₂.π = X₁.π ≫ f)
(r : X₁.R ⟶ X₂.R)
(fst : r ≫ X₂.fst = X₁.fst ≫ g)
(snd : r ≫ X₂.snd = X₁.snd ≫ g)

attribute [simp, reassoc, elementwise]
  prepresentation.hom_over.hg
  prepresentation.hom_over.fst
  prepresentation.hom_over.snd

local attribute [simp, elementwise]
  Profinite.pullback.condition
  Profinite.pullback.condition_assoc

def prepresentation.hom_over.comp {B₁ B₂ B₃ : Profinite.{u}}
  {X₁ : B₁.prepresentation} {X₂ : B₂.prepresentation} {X₃ : B₃.prepresentation}
  {f₁ : B₁ ⟶ B₂} {f₂ : B₂ ⟶ B₃}
  (e₁ : X₁.hom_over X₂ f₁) (e₂ : X₂.hom_over X₃ f₂) :
  X₁.hom_over X₃ (f₁ ≫ f₂) :=
{ g := e₁.g ≫ e₂.g,
  hg := by simp,
  r := e₁.r ≫ e₂.r,
  fst := by simp,
  snd := by simp }

def prepresentation.pullback_G {X B : Profinite} (f : X ⟶ B) (hf : function.surjective f)
  (P : B.prepresentation) : X.prepresentation :=
{ G := Profinite.pullback f P.π,
  π := Profinite.pullback.fst _ _,
  hπ := begin
    intros x,
    obtain ⟨y,hy⟩ := P.hπ (f x),
    exact ⟨⟨⟨x,y⟩,hy.symm⟩,rfl⟩,
  end,
  R := Profinite.pullback f P.base,
  r := Profinite.pullback.lift _ _
    (Profinite.pullback.lift _ _
      (Profinite.pullback.fst _ _)
      (Profinite.pullback.snd _ _ ≫ P.fst) $ by simp)
    (Profinite.pullback.lift _ _
      (Profinite.pullback.fst _ _)
      (Profinite.pullback.snd _ _ ≫ P.snd) $ by simp) $ by simp,
  hr := begin
    rintros ⟨⟨⟨⟨a,b₁⟩,h₁⟩,⟨⟨a₂,b₂⟩,h₂⟩⟩,(rfl : a = a₂)⟩,
    dsimp at h₁ h₂,
    let c : Profinite.pullback P.π P.π := ⟨⟨b₁,b₂⟩,_⟩,
    swap, { dsimp, rw [← h₁, ← h₂] },
    obtain ⟨d,hd⟩ := P.hr c,
    refine ⟨⟨⟨a,d⟩,_⟩,_⟩,
    { dsimp only [prepresentation.base, prepresentation.snd],
      dsimp,
      rwa hd },
    { dsimp [prepresentation.fst, prepresentation.snd],
      congr,
      { simp [hd] },
      { simp [hd] } },
  end } .

def presentation.pullback_R {X B : Profinite} (f : X ⟶ B) (hf : function.surjective f)
  (P : B.prepresentation) : (Profinite.pullback f f).prepresentation :=
{ G := Profinite.pullback (Profinite.pullback.snd f f ≫ f) P.π,
  π := Profinite.pullback.lift _ _
    (Profinite.pullback.fst _ _ ≫ Profinite.pullback.fst _ _)
    (Profinite.pullback.fst _ _ ≫ Profinite.pullback.snd _ _) $ by simp,
  hπ := begin
    rintros ⟨⟨a,b⟩,h⟩,
    dsimp at h,
    obtain ⟨c,hc⟩ := P.hπ (f b),
    refine ⟨⟨⟨⟨⟨a,b⟩,h⟩,c⟩,hc.symm⟩,_⟩,
    refl,
  end,
  R := Profinite.pullback (Profinite.pullback.snd f f ≫ f) P.base,
  r := Profinite.pullback.lift _ _
    (Profinite.pullback.lift _ _
      (Profinite.pullback.fst _ _)
      (Profinite.pullback.snd _ _ ≫ P.fst) $ by simp)
    (Profinite.pullback.lift _ _
      (Profinite.pullback.fst _ _)
      (Profinite.pullback.snd _ _ ≫ P.snd) $ by simp) $
      by { apply Profinite.pullback.hom_ext; simp },
  hr := begin
    rintros ⟨⟨⟨⟨⟨⟨a₁,a₁'⟩,h₁'⟩,b₁⟩,h₁⟩,⟨⟨⟨⟨a₂,a₂'⟩,h₂'⟩,b₂⟩,h₂⟩⟩,h⟩,
    change f a₁' = (P.π) b₁ at h₁,
    change f a₂' = (P.π) b₂ at h₂,
    change f a₁ = f a₁' at h₁',
    change f a₂ = f a₂' at h₂',
    change _ = _ at h,
    have hfst := h,
    have hsnd := h,
    apply_fun (λ a, a.1.1) at hfst,
    apply_fun (λ a, a.1.2) at hsnd,
    change a₁ = a₂ at hfst,
    change a₁' = a₂' at hsnd,
    let e : Profinite.pullback f f := ⟨⟨a₁,a₁'⟩, h₁'⟩,
    let w₀ : Profinite.pullback P.π P.π := ⟨⟨b₁,b₂⟩,_⟩,
    swap, { change _ = _, rw [← h₁, ← h₂, hsnd] },
    obtain ⟨w₁,hw₁⟩ := P.hr w₀,
    let w : Profinite.pullback (pullback.snd f f ≫ f) P.base := ⟨⟨e,w₁⟩,_⟩,
    swap, { change _ = _, change f _ = P.π (pullback.snd _ _ _),
      erw hw₁,
      dsimp only [pullback.fst_apply, e, pullback.snd_apply], rw hsnd, exact h₂ },
    use w,
    dsimp only [w, e, pullback.fst_apply, pullback.snd_apply, pullback.lift_apply],
    congr,
    { dsimp [prepresentation.fst],
      rw hw₁, refl },
    { congr' 2 },
    { dsimp [prepresentation.snd],
      rw hw₁, refl },
  end } .

def prepresentation.pullback_π {X B : Profinite}
  (f : X ⟶ B) (hf : function.surjective f)
  (P : B.prepresentation) : (P.pullback_G f hf).hom_over P f :=
{ g := Profinite.pullback.snd _ _,
  hg := begin
    dsimp [prepresentation.pullback_G],
    simp,
  end,
  r := Profinite.pullback.snd _ _,
  fst := begin
    dsimp [prepresentation.pullback_G, prepresentation.fst],
    simp,
  end,
  snd := begin
    dsimp [prepresentation.pullback_G, prepresentation.snd],
    simp,
  end }

lemma prepresentation.pullback_π_g_surjective {X B : Profinite}
  (f : X ⟶ B) (hf : function.surjective f)
  (P : B.prepresentation) :
  function.surjective (P.pullback_π f hf).g :=
begin
  intros x,
  obtain ⟨y,hy⟩ := hf (P.π x),
  exact ⟨⟨⟨y,x⟩,hy⟩,rfl⟩,
end

lemma prepresentation.pullback_π_r_surjective {X B : Profinite}
  (f : X ⟶ B) (hf : function.surjective f)
  (P : B.prepresentation) :
  function.surjective (P.pullback_π f hf).r :=
begin
  intros x,
  obtain ⟨y,hy⟩ := hf (P.base x),
  exact ⟨⟨⟨y,x⟩,hy⟩,rfl⟩
end

end Profinite
-/
