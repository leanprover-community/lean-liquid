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

@[ext]
lemma cover.ext (X : C) (S T : J.cover X) (h : (S : sieve X) = T) : S = T :=
subtype.ext h

variable {J}
lemma cover.condition {X : C} (S : J.cover X) : (S : sieve X) ∈ J X := S.2
variable (J)

@[simps]
def cover.map {X Y : C} (f : X ⟶ Y) : J.cover Y ⥤ J.cover X :=
{ obj := λ S, ⟨(S : sieve Y).pullback f, J.pullback_stable _ S.condition⟩,
  map := λ S T h, hom_of_le $ sieve.pullback_monotone _ $ le_of_hom h }

def cover.map_id (X : C) : cover.map J (𝟙 X) ≅ 𝟭 _ :=
nat_iso.of_components (λ I, eq_to_iso $ by { ext, simp }) $ by tidy

def cover.map_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  cover.map J (f ≫ g) ≅ cover.map J g ⋙ cover.map J f :=
nat_iso.of_components (λ I, eq_to_iso $ by { ext, simp }) $ by tidy

def cover.top (X : C) : J.cover X := ⟨⊤, J.top_mem _⟩

def cover.map_top {X Y : C} (f : X ⟶ Y) :
  (cover.map J f).obj (cover.top _ _) ≅ cover.top _ _ :=
eq_to_iso rfl

def cover.to_top (X : C) (S : J.cover X) : S ⟶ cover.top _ _ :=
⟨⟨le_top⟩⟩

instance (X : C) : is_cofiltered (J.cover X) :=
{ cocone_objs := λ A B, ⟨⟨A ⊓ B, J.intersection_covering A.condition B.condition⟩,
    hom_of_le inf_le_left, hom_of_le inf_le_right, by tauto⟩,
  cocone_maps := λ A B f g, ⟨A, 𝟙 _, rfl⟩,
  nonempty := ⟨cover.top J X⟩ }

variable {J}

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

def cover.map_left {X Y : C} (f : X ⟶ Y) (S : J.cover Y) :
  ((cover.map J f).obj S).left → S.left :=
λ I, ⟨I.Y, I.f ≫ f, I.hf⟩

def cover.map_right {X Y : C} (f : X ⟶ Y) (S : J.cover Y) :
  ((cover.map J f).obj S).right → S.right :=
λ I, ⟨I.Y₁, I.Y₂, I.Z, I.g₁, I.g₂, I.f₁ ≫ f, I.f₂ ≫ f, I.h₁, I.h₂, by simp [reassoc_of I.w]⟩

@[simp]
lemma cover.map_left_f {X Y : C} (f : X ⟶ Y) (S : J.cover Y)
  (t : ((cover.map J f).obj S).left) :
  (cover.map_left f S t).f = t.f ≫ f := rfl

@[simp]
lemma cover.fst_right_map {X : C} {S T : J.cover X} (h : S ⟶ T) (x : S.right) :
   (cover.left_map h) (cover.fst _ x) = cover.fst _ (cover.right_map h x) := rfl

@[simp]
lemma cover.snd_right_map {X : C} {S T : J.cover X} (h : S ⟶ T) (x : S.right) :
   (cover.left_map h) (cover.snd _ x) = cover.snd _ (cover.right_map h x) := rfl

@[simp]
lemma cover.map_left_map {X Y : C} (f : X ⟶ Y) (S T : J.cover Y) (h : S ⟶ T)
  (t : ((cover.map J f).obj S).left) :
  cover.map_left f _ (cover.left_map ((cover.map J f).map h) t) =
  cover.left_map h (cover.map_left f _ t) := rfl

@[simp]
lemma cover.map_right_map {X Y : C} (f : X ⟶ Y) (S T : J.cover Y) (h : S ⟶ T)
  (t : ((cover.map J f).obj S).right) :
  cover.map_right f _ (cover.right_map ((cover.map J f).map h) t) =
  cover.right_map h (cover.map_right f _ t) := rfl

noncomputable theory

open opposite

def cover.index {X : C} (S : J.cover X) : multipair.index S.fst S.snd D :=
{ L := λ I, P.obj (op I.Y),
  R := λ I, P.obj (op I.Z),
  F := λ I, P.map I.g₁.op,
  S := λ I, P.map I.g₂.op }

def cover.multifork {X : C} (S : J.cover X) :
  multifork (S.index P) :=
multifork.of_ι _ (P.obj (op X)) (λ I, P.map I.f.op) begin
  intros II,
  dsimp [cover.index],
  simp_rw [← P.map_comp, ← op_comp],
  congr' 2,
  apply II.w,
end

def cover.family_of_elements {X : C} (S : J.cover X) (K : multifork (S.index P)) :
  presieve.family_of_elements (P ⋙ coyoneda.obj (op K.X)) S :=
λ Y f hf, K.ι ⟨Y,f,hf⟩

lemma cover.compatible {X : C} (S : J.cover X) (K : multifork (S.index P)) :
  (S.family_of_elements P K).compatible :=
begin
  intros Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w,
  dsimp [cover.family_of_elements],
  erw K.w (walking_multipair.hom.fst ⟨Y₁, Y₂, Z, g₁, g₂, f₁, f₂, h₁, h₂, w⟩),
  erw K.w (walking_multipair.hom.snd ⟨Y₁, Y₂, Z, g₁, g₂, f₁, f₂, h₁, h₂, w⟩),
end

def cover.diagram_obj {X : C} (S : J.cover X) [has_limits D] : D :=
multiequalizer (S.index P)

def cover.diagram_map [has_limits D] {X : C} (S T : J.cover X) (h : S ⟶ T) :
  T.diagram_obj P ⟶ S.diagram_obj P :=
multiequalizer.lift _
(λ I, multiequalizer.ι _ (cover.left_map h I) ≫ P.map (𝟙 _)) begin
  intros I,
  dsimp,
  simp only [functor.map_id, category.assoc],
  erw [category.id_comp, category.id_comp],
  apply multiequalizer.condition
end

variable (J)
def cover_diagram [has_limits D] (X : C) : (J.cover X)ᵒᵖ ⥤ D :=
{ obj := λ I, I.unop.diagram_obj P,
  map := λ _ _ h, cover.diagram_map P _ _ h.unop,
  map_id' := begin
    intros I,
    dsimp [cover.diagram_map],
    ext T,
    simp only [functor.map_id, multiequalizer.lift_ι, category.id_comp, category.comp_id],
    erw category.comp_id,
    congr' 1,
    tidy,
  end,
  map_comp' := begin
    intros A B C e h,
    dsimp [cover.diagram_map],
    ext T,
    simp only [functor.map_id, multiequalizer.lift_ι, multiequalizer.lift_ι_assoc, category.assoc],
    erw [category.comp_id, category.comp_id, category.comp_id],
    simpa,
  end }

def cover_diagram.map [has_limits D] {X Y : C} (f : X ⟶ Y) :
   cover_diagram J P Y ⟶ (cover.map J f).op ⋙ cover_diagram J P X :=
{ app := λ I, multiequalizer.lift _
    (λ t, multiequalizer.ι _ (cover.map_left f _ t)) begin
      intros II,
      exact multiequalizer.condition _ (cover.map_right _ _ II),
    end,
  naturality' := begin
    intros A B h,
    dsimp [cover_diagram, cover.diagram_map],
    ext t,
    simp only [functor.map_id, multiequalizer.lift_ι, multiequalizer.lift_ι_assoc, category.assoc],
    erw [category.comp_id],
  end }

def plus_obj [has_limits D] [has_colimits D] (X : C) : D :=
colimit (J.cover_diagram P X)

def plus_map [has_limits D] [has_colimits D] {X Y : C} (f : X ⟶ Y) :
J.plus_obj P Y ⟶ J.plus_obj P X :=
colim_map (cover_diagram.map J P f) ≫ colimit.pre _ _

def plus [has_limits D] [has_colimits D] : Cᵒᵖ ⥤ D :=
{ obj := λ X, plus_obj J P X.unop,
  map := λ X Y f, plus_map J P f.unop,
  map_id' := begin
    intros X,
    ext I,
    dsimp [plus_map],
    simp only [colimit.ι_pre, ι_colim_map_assoc],
    let e : I ≅ (cover.map J (𝟙 (unop X))).op.obj I :=
      (nat_iso.op (cover.map_id J X.unop)).app I,
    erw [← colimit.w (J.cover_diagram P X.unop) e.inv, category.comp_id, ← category.assoc],
    convert category.id_comp _ using 1,
    congr' 1,
    dsimp [cover_diagram.map],
    ext,
    dsimp [cover_diagram, cover.diagram_map],
    simp only [functor.map_id, multiequalizer.lift_ι, category.id_comp,
      category.comp_id, category.assoc],
    erw [category.comp_id, multiequalizer.lift_ι],
    congr' 1,
    tidy,
  end,
  map_comp' := begin
    intros A B C e h,
    ext I,
    dsimp [plus_map],
    simp only [colimit.ι_pre_assoc, colimit.ι_pre, ι_colim_map_assoc, category.assoc],
    let e : (cover.map J h.unop).op.obj ((cover.map J e.unop).op.obj I) ≅
      (cover.map J (h.unop ≫ e.unop)).op.obj I :=
      (nat_iso.op (cover.map_comp J _ _)).app I,
    simp_rw [← colimit.w (J.cover_diagram P _) e.inv, ← category.assoc],
    congr' 1,
    ext,
    dsimp [cover_diagram.map, cover_diagram, cover.diagram_map],
    simp only [functor.map_id, multiequalizer.lift_ι, category.comp_id, category.assoc],
    erw [category.comp_id, multiequalizer.lift_ι],
    congr' 1,
    tidy,
  end }

def to_plus_app [has_limits D] [has_colimits D] (X : C) :
  P.obj (op X) ⟶ plus_obj J P X :=
multiequalizer.lift ((cover.top J X).index P) (λ I, P.map I.f.op)
  begin
    intros I,
    dsimp [cover.index],
    simp_rw [← P.map_comp, ← op_comp],
    congr' 2,
    apply I.w
  end
≫ colimit.ι (J.cover_diagram P X) (op $ cover.top _ _)

def to_plus [has_limits D] [has_colimits D] :
  P ⟶ plus J P :=
{ app := λ X, to_plus_app J P X.unop,
  naturality' := begin
    intros X Y f,
    dsimp [to_plus_app, plus, plus_map],
    simp,
    dsimp [cover_diagram.map],
    let e : (cover.map J f.unop).obj (cover.top J X.unop)
      ⟶ cover.top J Y.unop := cover.to_top _ _ _,
    simp_rw [← colimit.w _ e.op, ← category.assoc],
    congr' 1,
    dsimp [cover_diagram, cover.diagram_map],
    ext,
    simp only [cover.map_left_f, functor.map_id,
      multiequalizer.lift_ι, op_comp, category.comp_id,
      quiver.hom.op_unop, functor.map_comp, category.assoc],
    erw [category.comp_id, multiequalizer.lift_ι],
    refl,
  end }

end grothendieck_topology
end category_theory
