import category_theory.sites.sheaf_of_types
import category_theory.sites.grothendieck
import category_theory.filtered
import category_theory.limits.shapes.multiequalizer

namespace category_theory.grothendieck_topology

open category_theory
open category_theory.limits
open opposite

universes w v u
variables {C : Type u} [category.{v} C] (J : grothendieck_topology C)
variables {D : Type w} [category.{max v u} D] (P : Cᵒᵖ ⥤ D)

@[derive [preorder]]
def cover (X : C) := { S : sieve X // S ∈ J X }

namespace cover

variables {J} {X Y : C}

instance : has_coe (J.cover X) (sieve X) := ⟨λ S, S.1⟩

instance : has_coe_to_fun (J.cover X) (λ S, Π ⦃Y : C⦄ (f : Y ⟶ X), Prop) :=
⟨λ S Y f, (S : sieve X) f⟩

@[simp]
lemma coe_coe (S : J.cover X) ⦃Y⦄ (f : Y ⟶ X) : (S : sieve X) f = S f := rfl

lemma condition (S : J.cover X) : (S : sieve X) ∈ J X := S.2

@[ext]
lemma ext (S T : J.cover X) (h : ∀ ⦃Y : C⦄ (f : Y ⟶ X), S f ↔ T f) : S = T :=
subtype.ext $ sieve.ext h

instance : semilattice_inf_top (J.cover X) :=
{ top := ⟨⊤, J.top_mem X⟩,
  le_antisymm := λ S T h1 h2, cover.ext _ _ $ λ Y f, ⟨h1 _, h2 _⟩,
  le_top := λ S Y f, by tauto,
  inf := λ S T, ⟨S ⊓ T, J.intersection_covering S.condition T.condition⟩,
  inf_le_left := λ S T Y f hf, hf.1,
  inf_le_right := λ S T Y f hf, hf.2,
  le_inf := λ S T Q h1 h2 Y f hf, ⟨h1 _ hf, h2 _ hf⟩,
  ..(infer_instance : preorder _) }

structure L (S : J.cover X) : Type (max v u) :=
(Y : C)
(f : Y ⟶ X)
(hf : S f)

def map_L {S T : J.cover X} (h : S ⟶ T) : S.L → T.L :=
λ I, ⟨I.Y, I.f, le_of_hom h _ I.hf⟩

structure R (S : J.cover X) : Type (max v u) :=
(Y₁ Y₂ Z : C)
(g₁ : Z ⟶ Y₁)
(g₂ : Z ⟶ Y₂)
(f₁ : Y₁ ⟶ X)
(f₂ : Y₂ ⟶ X)
(h₁ : S f₁)
(h₂ : S f₂)
(w : g₁ ≫ f₁ = g₂ ≫ f₂)

def map_R {S T : J.cover X} (h : S ⟶ T) : S.R → T.R :=
λ I, ⟨I.Y₁, I.Y₂, I.Z, I.g₁, I.g₂, I.f₁, I.f₂,
  le_of_hom h _ I.h₁, le_of_hom h _ I.h₂, I.w⟩

def index (S : J.cover X) : multicospan_index D :=
{ L := S.L,
  R := S.R,
  fst_to := λ I, ⟨I.Y₁, I.f₁, I.h₁⟩,
  snd_to := λ I, ⟨I.Y₂, I.f₂, I.h₂⟩,
  left := λ I, P.obj (op I.Y),
  right := λ I, P.obj (op I.Z),
  fst := λ I, P.map I.g₁.op,
  snd := λ I, P.map I.g₂.op }

def multifork (S : J.cover X) : multifork (S.index P) :=
multifork.of_ι _ (P.obj (op X)) (λ I, P.map I.f.op) begin
  intros I,
  dsimp [index],
  simp only [← P.map_comp, ← op_comp, I.w]
end

def family_of_elements (S : J.cover X) (E : limits.multifork (S.index P)) :
  presieve.family_of_elements (P ⋙ coyoneda.obj (op E.X)) S :=
λ Y f hf, E.ι ⟨_,f,hf⟩

lemma compatible (S : J.cover X) (E : limits.multifork (S.index P)) :
  (S.family_of_elements P E).compatible :=
begin
  intros Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w,
  dsimp [family_of_elements],
  erw E.w (walking_multicospan.hom.fst ⟨Y₁, Y₂, Z, g₁, g₂, f₁, f₂, h₁, h₂, w⟩),
  erw E.w (walking_multicospan.hom.snd ⟨Y₁, Y₂, Z, g₁, g₂, f₁, f₂, h₁, h₂, w⟩),
end

noncomputable abbreviation to_multiequalizer (S : J.cover X)
  [has_multiequalizer (S.index P)] : P.obj (op X) ⟶ multiequalizer (S.index P) :=
multiequalizer.lift _ _ (λ I, P.map I.f.op) $ begin
  intros I,
  dsimp [index],
  simp_rw [← P.map_comp, ← op_comp, I.w],
end

end cover

variables {X Y Z : C}

def pullback (f : X ⟶ Y) : J.cover Y ⥤ J.cover X :=
{ obj := λ S, ⟨(S : sieve Y).pullback f, J.pullback_stable _ S.condition⟩,
  map := λ S T f, hom_of_le $ sieve.pullback_monotone _ $ le_of_hom f }

@[simp]
lemma pullback_obj_apply (f : X ⟶ Y) (S : J.cover Y) : ∀ ⦃Z⦄ (g : Z ⟶ X),
  ((J.pullback f).obj S g) ↔ (S : sieve Y).pullback f g := by tidy

def pullback_id (X : C) : J.pullback (𝟙 X) ≅ 𝟭 _ :=
nat_iso.of_components (λ S, eq_to_iso $ by { ext, simp }) $ by tidy

def pullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
  J.pullback (f ≫ g) ≅ J.pullback g ⋙ J.pullback f :=
nat_iso.of_components (λ S, eq_to_iso $ by { ext, simp }) $ by tidy

@[simp]
def pullback_L (f : X ⟶ Y) (S : J.cover Y) : ((J.pullback f).obj S).L → S.L :=
λ I, ⟨I.Y, I.f ≫ f, I.hf⟩

@[simp]
def pullback_R (f : X ⟶ Y) (S : J.cover Y) : ((J.pullback f).obj S).R → S.R :=
λ I, ⟨I.Y₁, I.Y₂, I.Z, I.g₁, I.g₂, I.f₁ ≫ f, I.f₂ ≫ f, I.h₁, I.h₂, by simp [reassoc_of I.w]⟩

noncomputable theory

-- TODO: Can we get rid of the 𝟙 _ after the multiequalizer.ι here?
@[simps]
def diagram (X : C) [has_limits D] : (J.cover X)ᵒᵖ ⥤ D :=
{ obj := λ S, multiequalizer (S.unop.index P),
  map := λ S T e, multiequalizer.lift _ _ (λ I, multiequalizer.ι _ (cover.map_L e.unop I) ≫ 𝟙 _) $
    λ I, by simpa using multiequalizer.condition (S.unop.index P) (cover.map_R e.unop I),
  map_id' := begin
    intros S,
    ext ⟨_,_,_⟩,
    simpa,
  end,
  map_comp' := begin
    intros S T W f g,
    ext ⟨_,_,_⟩,
    simpa,
  end }

@[simps]
def diagram_pullback [has_limits D] {X Y : C} (f : X ⟶ Y) :
  J.diagram P Y ⟶ (J.pullback f).op ⋙ J.diagram P X :=
{ app := λ S, multiequalizer.lift (((J.pullback f).obj S.unop).index P) _
    (λ I, multiequalizer.ι (S.unop.index P) (J.pullback_L f _ I))
      (λ I, multiequalizer.condition (S.unop.index P) (J.pullback_R f _ I)),
  naturality' := begin
    intros A B e,
    dsimp,
    ext,
    simpa,
  end } .

-- TODO: Change to `has_filtered_colimits`
@[simps]
def plus_obj [has_limits D] [has_colimits D] : Cᵒᵖ ⥤ D :=
{ obj := λ X, colimit (J.diagram P X.unop),
  map := λ X Y f, colim_map (J.diagram_pullback P f.unop) ≫ colimit.pre _ _,
  map_id' := begin
    intros X,
    ext I,
    dsimp,
    simp only [diagram_pullback_app, colimit.ι_pre, ι_colim_map_assoc, category.comp_id],
    let e : (J.pullback (𝟙 X.unop)).op.obj I ≅ I :=
      ((nat_iso.op (J.pullback_id X.unop)).app I).symm,
    rw [← colimit.w _ e.hom, ← category.assoc],
    convert category.id_comp _,
    ext ⟨_,_,_⟩,
    dsimp,
    simp only [multiequalizer.lift_ι, category.id_comp, category.comp_id, category.assoc],
    congr,
    simpa,
  end,
  map_comp' := begin
    intros X Y Z f g,
    ext I,
    dsimp,
    simp only [diagram_pullback_app, colimit.ι_pre_assoc,
      colimit.ι_pre, ι_colim_map_assoc, category.assoc],
    let e : (J.pullback (g.unop ≫ f.unop)).op.obj I ≅
      (J.pullback g.unop).op.obj ((J.pullback f.unop).op.obj I) :=
      ((nat_iso.op (J.pullback_comp g.unop f.unop)).app I).symm,
    simp_rw [← colimit.w _ e.hom, ← category.assoc],
    congr' 1,
    ext II,
    dsimp,
    simp only [multiequalizer.lift_ι, category.comp_id, category.assoc],
    congr' 1,
    simpa,
  end } .

@[simps]
def plus_map [has_limits D] [has_colimits D] {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) :
  plus_obj J P ⟶ plus_obj J Q :=
{ app := λ X, colim_map $
  { app := λ I, multiequalizer.lift _ _ (λ II, multiequalizer.ι _ II ≫ η.app _) begin
      intros II,
      erw [category.assoc, category.assoc, ← η.naturality, ← η.naturality,
        ← category.assoc, ← category.assoc, multiequalizer.condition],
      refl,
    end,
    naturality' := begin
      intros I₁ I₂ e,
      dsimp,
      ext,
      simpa,
    end },
  naturality' := begin
    intros X Y f,
    dsimp,
    ext,
    simp only [diagram_pullback_app, ι_colim_map, colimit.ι_pre_assoc,
      colimit.ι_pre, ι_colim_map_assoc, category.assoc],
    simp_rw ← category.assoc,
    congr' 1,
    ext,
    dsimp,
    simp,
  end }

@[simps]
def plus [has_limits D] [has_colimits D] : (Cᵒᵖ ⥤ D) ⥤ (Cᵒᵖ ⥤ D) :=
{ obj := λ F, plus_obj J F,
  map := λ F G η, plus_map J η,
  map_id' := begin
    intros F,
    ext,
    dsimp,
    simp only [ι_colim_map, category.comp_id],
    convert category.id_comp _,
    ext,
    simp only [multiequalizer.lift_ι, category.id_comp],
    erw category.comp_id,
  end,
  map_comp' := begin
    intros F G H η γ,
    ext,
    dsimp,
    simp only [ι_colim_map, ι_colim_map_assoc],
    simp_rw ← category.assoc,
    congr' 1,
    ext,
    dsimp,
    simp,
  end }

@[simps]
def to_plus_app [has_limits D] [has_colimits D] :
  P ⟶ (plus_obj J P) :=
{ app := λ X, cover.to_multiequalizer P (⊤ : J.cover X.unop) ≫
    colimit.ι (J.diagram P X.unop) (op ⊤),
  naturality' := begin
    intros X Y f,
    dsimp,
    simp only [diagram_pullback_app, colimit.ι_pre, ι_colim_map_assoc, category.assoc],
    let e : (J.pullback f.unop).obj ⊤ ⟶ ⊤ := hom_of_le (semilattice_inf_top.le_top _),
    simp_rw [← colimit.w _ e.op, ← category.assoc],
    congr' 1,
    ext,
    dsimp,
    simp only [limit.lift_π, multifork.of_ι_π_app,
      multiequalizer.lift_ι, category.comp_id, category.assoc],
    dsimp [multifork.of_ι],
    simp_rw [← P.map_comp],
    refl,
  end } .

@[simps]
def to_plus [has_limits D] [has_colimits D] :
  (𝟭 (Cᵒᵖ ⥤ D)) ⟶ plus J :=
{ app := λ F, to_plus_app _ _,
  naturality' := begin
    intros F G η,
    ext,
    dsimp,
    simp only [ι_colim_map, category.assoc],
    simp_rw ← category.assoc,
    congr' 1,
    ext,
    dsimp,
    simp only [limit.lift_π, multifork.of_ι_π_app, limit.lift_π_assoc,
      multiequalizer.lift_ι, category.assoc],
    dsimp [multifork.of_ι],
    symmetry,
    apply η.naturality,
  end }

lemma map_to_plus [has_limits D] [has_colimits D] (P : Cᵒᵖ ⥤ D) :
  J.plus_map (J.to_plus_app P) = J.to_plus_app _ :=
begin
  -- TODO: GOLF THIS!
  ext X j,
  dsimp,
  simp,
  let e : j.unop ⟶ ⊤ := hom_of_le (semilattice_inf_top.le_top _),
  rw ← colimit.w _ e.op,
  simp only [← category.assoc],
  congr' 1,
  ext I,
  dsimp,
  simp,
  dsimp [multifork.of_ι],
  simp,
  delta cover.to_multiequalizer,
  dsimp [cover.map_L],
  let ee : (J.pullback I.f).obj (unop j) ⟶ ⊤ := hom_of_le (semilattice_inf_top.le_top _),
  rw ← colimit.w _ ee.op,
  simp only [← category.assoc],
  congr' 1,
  ext II,
  dsimp,
  simp,
  dsimp [multifork.of_ι, cover.map_L],
  let RR : j.unop.R :=
  { Y₁ := _,
    Y₂ := _,
    Z := _,
    g₁ := II.f,
    g₂ := 𝟙 _,
    f₁ := I.f,
    f₂ := II.f ≫ I.f,
    h₁ := I.hf,
    h₂ := sieve.downward_closed _ I.hf _,
    w := by simp },
  convert multiequalizer.condition (j.unop.index P) RR,
  { cases I, refl },
  { dsimp [cover.index, RR],
    simpa }
end

lemma plus_map_to_plus_app [has_limits D] [has_colimits D] (P : Cᵒᵖ ⥤ D) :
  J.plus.map (J.to_plus.app P) = J.to_plus.app (J.plus.obj P) :=
map_to_plus _ _

end category_theory.grothendieck_topology
