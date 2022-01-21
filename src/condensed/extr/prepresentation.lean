import topology.category.Profinite
import for_mathlib.Profinite.disjoint_union

namespace Profinite

universe u

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

def prepresentation.pullback {X B : Profinite} (f : X ⟶ B) (hf : function.surjective f)
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
    { dsimp [pullback.lift, pullback.fst, pullback.snd,
        prepresentation.fst, prepresentation.snd],
      congr,
      { simp [hd] },
      { simp [hd] } },
  end } .

def prepresentation.pullback_hom_over {X B : Profinite}
  (f : X ⟶ B) (hf : function.surjective f)
  (P : B.prepresentation) : (P.pullback f hf).hom_over P f :=
{ g := Profinite.pullback.snd _ _,
  hg := begin
    dsimp [prepresentation.pullback],
    simp,
  end,
  r := Profinite.pullback.snd _ _,
  fst := begin
    dsimp [prepresentation.pullback, prepresentation.fst],
    simp,
  end,
  snd := begin
    dsimp [prepresentation.pullback, prepresentation.snd],
    simp,
  end }

lemma prepresentation.pullback_hom_over_g_surjective {X B : Profinite}
  (f : X ⟶ B) (hf : function.surjective f)
  (P : B.prepresentation) :
  function.surjective (P.pullback_hom_over f hf).g :=
begin
  intros x,
  obtain ⟨y,hy⟩ := hf (P.π x),
  exact ⟨⟨⟨y,x⟩,hy⟩,rfl⟩,
end

lemma prepresentation.pullback_hom_over_r_surjective {X B : Profinite}
  (f : X ⟶ B) (hf : function.surjective f)
  (P : B.prepresentation) :
  function.surjective (P.pullback_hom_over f hf).r :=
begin
  intros x,
  obtain ⟨y,hy⟩ := hf (P.base x),
  exact ⟨⟨⟨y,x⟩,hy⟩,rfl⟩
end

end Profinite
