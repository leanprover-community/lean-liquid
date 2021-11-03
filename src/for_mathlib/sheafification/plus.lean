import category_theory.sites.sheaf

import for_mathlib.sheafification.multifork

namespace category_theory
namespace grothendieck_topology

open category_theory.limits

universes w v u
variables {C : Type u} [category.{v} C] (J : grothendieck_topology C)
variables {D : Type w} [category.{max v u} D] (P : Cᵒᵖ ⥤ D)

@[derive small_category]
def cover (X : C) := { S : sieve X // S ∈ J X }

instance (X : C) : has_coe (J.cover X) (sieve X) := ⟨λ S, S.1⟩

instance (X : C) : has_coe_to_fun (J.cover X) (λ S, Π ⦃Y⦄ (f : Y ⟶ X), Prop) :=
⟨λ S Y f, (S : sieve X) f⟩

variable {J}
lemma cover.condition {X : C} (S : J.cover X) : (S : sieve X) ∈ J X := S.2

instance (X : C) : is_cofiltered (J.cover X) :=
{ cocone_objs := λ A B, ⟨⟨A ⊓ B, J.intersection_covering A.condition B.condition⟩,
    hom_of_le inf_le_left, hom_of_le inf_le_right, by tauto⟩,
  cocone_maps := λ A B f g, ⟨A, 𝟙 _, rfl⟩,
  nonempty := ⟨⟨⊤, J.top_mem _⟩⟩ }

@[ext]
structure cover.left {X : C} (S : J.cover X) : Type (max v u) :=
(Y : C)
(f : Y ⟶ X)
(hf : S f)

@[ext]
structure cover.right {X : C} (S : J.cover X) : Type (max v u) :=
(Y₁ Y₂ Z : C)
(g₁ : Z ⟶ Y₁)
(g₂ : Z ⟶ Y₂)
(f₁ : Y₁ ⟶ X)
(f₂ : Y₂ ⟶ X)
(h₁ : S f₁)
(h₂ : S f₂)
(w : g₁ ≫ f₁ = g₂ ≫ f₂)

def cover.left_map {X : C} {S T : J.cover X} (h : S ⟶ T) : S.left → T.left :=
λ I, ⟨I.Y, I.f, le_of_hom h _ I.hf⟩

def cover.right_map {X : C} {S T : J.cover X} (h : S ⟶ T) : S.right → T.right :=
λ I, ⟨I.Y₁, I.Y₂, I.Z, I.g₁, I.g₂, I.f₁, I.f₂, le_of_hom h _ I.h₁, le_of_hom h _ I.h₂, I.w⟩

def cover.fst {X : C} (S : J.cover X) : S.right → S.left :=
λ I, ⟨I.Y₁, I.f₁, I.h₁⟩

def cover.snd {X : C} (S : J.cover X) : S.right → S.left :=
λ I, ⟨I.Y₂, I.f₂, I.h₂⟩

noncomputable theory

open opposite

def cover.diagram_obj {X : C} (S : J.cover X) [has_limits D] : D :=
multiequalizer
S.fst S.snd
(λ I : S.left, P.obj (op I.Y))
(λ I : S.right, P.obj (op I.Z))
(λ I, P.map I.g₁.op)
(λ I, P.map I.g₂.op)

def cover.diagram_map [has_limits D] {X : C} (S T : J.cover X) (h : S ⟶ T) :
  T.diagram_obj P ⟶ S.diagram_obj P :=
multiequalizer.lift _ _ _ _ _ _
(λ I, multiequalizer.ι _ _ _ _ _ _ (cover.left_map h I) ≫ P.map (𝟙 _)) begin
  intros I,
  dsimp,
  simpa using multiequalizer.condition T.fst T.snd
    (λ I, P.obj (op I.Y)) (λ I, P.obj (op I.Z))
    (λ I, P.map I.g₁.op) (λ I, P.map I.g₂.op)  (cover.right_map h I),
end

variable (J)
def cover_diagram [has_limits D] (X : C) : (J.cover X)ᵒᵖ ⥤ D :=
{ obj := λ I, I.unop.diagram_obj P,
  map := λ _ _ h, cover.diagram_map P _ _ h.unop,
  map_id' := begin
    intros I,
    dsimp [cover.diagram_map],
    ext T,
    dsimp,
    simp only [functor.map_id, multiequalizer.lift_ι, category.id_comp, category.comp_id],
    congr' 1,
    tidy,
  end,
  map_comp' := begin
    intros A B C e h,
    dsimp [cover.diagram_map],
    ext T,
    dsimp,
    simpa,
  end }

def plus_obj [has_limits D] [has_colimits D] (X : C) : D :=
colimit (J.cover_diagram P X)

def plus_map [has_limits D] [has_colimits D] {X Y : C} (f : X ⟶ Y) :
J.plus_obj P Y ⟶ J.plus_obj P X := sorry

end grothendieck_topology
end category_theory
