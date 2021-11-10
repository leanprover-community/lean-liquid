import category_theory.limits.concrete_category
import for_mathlib.sheafification.plus_sheaf_condition
import for_mathlib.concrete_filtered
import for_mathlib.concrete_multiequalizer

noncomputable theory

namespace category_theory.grothendieck_topology

open category_theory
open category_theory.limits
open opposite

universes w v u
variables {C : Type u} [category.{v} C] {D : Type w}
  [category.{max v u} D] {J : grothendieck_topology C}

variables [has_limits D] [has_colimits D]
variables [concrete_category.{max v u} D]
variables [preserves_limits (forget D)]
variables [∀ (X : C), preserves_colimits_of_shape (J.cover X)ᵒᵖ (forget D)]
variables [reflects_isomorphisms (forget D)]

local attribute [instance]
  concrete_category.has_coe_to_sort concrete_category.has_coe_to_fun

namespace plus

def meq {X : C} (P : Cᵒᵖ ⥤ D) (S : J.cover X) :=
{ x : Π (I : S.L), P.obj (op I.Y) //
  ∀ (I : S.R), P.map I.g₁.op (x ⟨_, I.f₁, I.h₁⟩) = P.map I.g₂.op (x ⟨_, I.f₂, I.h₂⟩) }

namespace meq

instance {X} (P : Cᵒᵖ ⥤ D) (S : J.cover X) : has_coe_to_fun (meq P S)
  (λ x, Π (I : S.L), P.obj (op I.Y)) := ⟨λ x, x.1⟩

@[ext]
lemma ext {X} {P : Cᵒᵖ ⥤ D} {S : J.cover X} (x y : meq P S)
  (h : ∀ I : S.L, x I = y I) : x = y := subtype.ext $ funext $ h

lemma condition {X} {P : Cᵒᵖ ⥤ D} {S : J.cover X} (x : meq P S) (I : S.R) :
  P.map I.g₁.op (x ((S.index P).fst_to I)) = P.map I.g₂.op (x ((S.index P).snd_to I)) := x.2 _

lemma condition' {X} {P : Cᵒᵖ ⥤ D} {S : J.cover X} (x : meq P S) (I : S.R) :
  P.map I.g₁.op (x ⟨_, I.f₁, I.h₁⟩) = P.map I.g₂.op (x ⟨_, I.f₂, I.h₂⟩) := x.2 _

def refine {X : C} {P : Cᵒᵖ ⥤ D} {S T : J.cover X} (x : meq P T) (e : S ⟶ T) :
  meq P S :=
⟨λ I, x ⟨I.Y, I.f, (le_of_hom e) _ I.hf⟩,
  λ I, x.condition' ⟨I.Y₁, I.Y₂, I.Z, I.g₁, I.g₂, I.f₁, I.f₂,
    (le_of_hom e) _ I.h₁, (le_of_hom e) _ I.h₂, I.w⟩⟩

@[simp]
lemma refine_apply {X : C} {P : Cᵒᵖ ⥤ D} {S T : J.cover X} (x : meq P T) (e : S ⟶ T)
  (I : S.L) : x.refine e I = x ⟨I.Y, I.f, (le_of_hom e) _ I.hf⟩ := rfl

def pullback {Y X : C} {P : Cᵒᵖ ⥤ D} {S : J.cover X} (x : meq P S) (f : Y ⟶ X) :
  meq P ((J.pullback f).obj S) :=
⟨λ I, x ⟨_,I.f ≫ f, I.hf⟩, λ I, x.condition
  ⟨I.Y₁, I.Y₂, I.Z, I.g₁, I.g₂, I.f₁ ≫ f, I.f₂ ≫ f, I.h₁, I.h₂, by simp [reassoc_of I.w]⟩ ⟩

@[simp]
lemma pullback_apply {Y X : C} {P : Cᵒᵖ ⥤ D} {S : J.cover X} (x : meq P S) (f : Y ⟶ X)
  (I : ((J.pullback f).obj S).L) : x.pullback f I = x ⟨_, I.f ≫ f, I.hf⟩ := rfl

@[simp]
lemma pullback_refine {Y X : C} {P : Cᵒᵖ ⥤ D} {S T : J.cover X} (h : S ⟶ T)
  (f : Y ⟶ X) (x : meq P T) : (x.pullback f).refine
  ((J.pullback f).map h) = (refine x h).pullback _ := rfl

def equiv_aux {X : C} (P : Cᵒᵖ ⥤ D) (S : J.cover X) :
  ((S.index P).multicospan ⋙ (forget D)).sections ≃ meq P S :=
{ to_fun := λ x, ⟨λ I, x.1 (walking_multicospan.left _), begin
    intros I,
    have a := x.2 (walking_multicospan.hom.fst I),
    have b := x.2 (walking_multicospan.hom.snd I),
    rw ← b at a,
    exact a,
  end⟩,
  inv_fun := λ x,
  { val := λ t,
    match t with
    | walking_multicospan.left a := x _
    | walking_multicospan.right b := P.map b.g₁.op (x ⟨_, b.f₁, b.h₁⟩)
    end,
    property := begin
      rintros (a|b) (a'|b') (f|f|f),
      { change ((S.index P).multicospan.map (𝟙 _)) _ = _, simp },
      { refl },
      { dsimp, erw ← x.condition b', refl },
      { change ((S.index P).multicospan.map (𝟙 _)) _ = _, simp },
    end },
  left_inv := begin
    intros x, ext (a|b),
    { refl },
    { change _ = x.val _,
      rw ← x.2 (walking_multicospan.hom.fst b),
      refl }
  end,
  right_inv := by { intros x, ext i, refl } }

def equiv {X : C} (P : Cᵒᵖ ⥤ D) (S : J.cover X) :
  (multiequalizer (S.index P) : D) ≃ meq P S :=
let h1 := (limit.is_limit (S.index P).multicospan),
    h2 := (is_limit_of_preserves (forget D) h1),
    E := h2.cone_point_unique_up_to_iso (types.limit_cone_is_limit _) in
equiv.trans E.to_equiv (equiv_aux P S)

@[simp]
lemma equiv_apply {X : C} {P : Cᵒᵖ ⥤ D} {S : J.cover X} (x : multiequalizer (S.index P))
  (I : S.L) : equiv P S x I = multiequalizer.ι (S.index P) I x := rfl

@[simp]
lemma equiv_symm_eq_apply {X : C} {P : Cᵒᵖ ⥤ D} {S : J.cover X} (x : meq P S) (I : S.L) :
  multiequalizer.ι (S.index P) I ((meq.equiv P S).symm x) = x I :=
begin
  let z := (meq.equiv P S).symm x,
  rw ← equiv_apply,
  simp,
end

def mk {X : C} {P : Cᵒᵖ ⥤ D} (S : J.cover X) (x : P.obj (op X)) : meq P S :=
⟨λ I, P.map I.f.op x, λ I, by { dsimp, simp only [← comp_apply, ← P.map_comp, ← op_comp, I.w] }⟩

lemma mk_apply {X : C} {P : Cᵒᵖ ⥤ D} (S : J.cover X) (x : P.obj (op X)) (I : S.L) :
  mk S x I = P.map I.f.op x := rfl

end meq

def mk {X : C} {P : Cᵒᵖ ⥤ D} {S : J.cover X} (x : meq P S) : (J.plus_obj P).obj (op X) :=
colimit.ι (J.diagram P X) (op S) ((meq.equiv P S).symm x)

lemma exists_rep {X : C} {P : Cᵒᵖ ⥤ D} (x : (J.plus_obj P).obj (op X)) :
  ∃ (S : J.cover X) (y : meq P S), x = mk y :=
begin
  obtain ⟨S,y,h⟩ := concrete.colimit_exists_rep (J.diagram P X) x,
  use [S.unop],
  dsimp [diagram] at y,
  use meq.equiv _ _ y,
  rw ← h,
  dsimp [mk],
  simp,
end

@[simp]
lemma res_mk_eq_mk_pullback {Y X : C} {P : Cᵒᵖ ⥤ D} {S : J.cover X} (x : meq P S) (f : Y ⟶ X) :
  (J.plus_obj P).map f.op (mk x) = mk (x.pullback f) :=
begin
  dsimp [mk],
  simp only [← comp_apply],
  simp only [comp_apply, colimit.ι_pre, ι_colim_map_assoc],
  congr' 1,
  apply_fun meq.equiv P _,
  swap, { apply_instance },
  erw equiv.apply_symm_apply,
  ext i,
  simp only [grothendieck_topology.diagram_pullback_app,
    meq.pullback_apply, meq.equiv_apply, ← comp_apply],
  erw [multiequalizer.lift_ι, meq.equiv_symm_eq_apply],
  cases i, refl,
end

lemma to_plus_mk {X : C} {P : Cᵒᵖ ⥤ D} (S : J.cover X) (x : P.obj (op X)) :
  (J.to_plus_app P).app _ x = mk (meq.mk S x) :=
begin
  dsimp [mk],
  let e : S ⟶ ⊤ := hom_of_le (semilattice_inf_top.le_top _),
  rw ← colimit.w _ e.op,
  delta cover.to_multiequalizer,
  simp only [comp_apply],
  congr' 1,
  dsimp [diagram],
  apply concrete.multiequalizer.eq_of_forall_eq _ _ (limit.is_limit _),
  swap, { apply_instance },
  intros i,
  change multiequalizer.ι (S.index P) i _ = multiequalizer.ι (S.index P) i _,
  simp only [← comp_apply, category.assoc, multiequalizer.lift_ι,
    category.comp_id, meq.equiv_symm_eq_apply],
  refl,
end

lemma to_plus_apply {X : C} {P : Cᵒᵖ ⥤ D} {S : J.cover X} (x : meq P S) (I : S.L) :
  (J.to_plus_app P).app _ (x I) = (J.plus_obj P).map I.f.op (mk x) :=
begin
  dsimp only [to_plus_app],
  delta cover.to_multiequalizer,
  dsimp [mk],
  simp only [← comp_apply],
  simp only [comp_apply, colimit.ι_pre, ι_colim_map_assoc],
  dsimp only [functor.op],
  let e : (J.pullback I.f).obj (unop (op S)) ⟶ ⊤ := hom_of_le (semilattice_inf_top.le_top _),
  rw ← colimit.w _ e.op,
  simp only [comp_apply],
  congr' 1,
  apply concrete.multiequalizer.eq_of_forall_eq _ _ (limit.is_limit _),
  swap, { apply_instance },
  intros i,
  change multiequalizer.ι (((J.pullback I.f).obj S).index P) i _ =
    multiequalizer.ι (((J.pullback I.f).obj S).index P) i _,
  dsimp [diagram],
  simp only [← comp_apply, category.assoc, multiequalizer.lift_ι,
    category.comp_id, meq.equiv_symm_eq_apply],
  dsimp [cover.map_L],
  let RR : S.R :=
  { Y₁ := _,
    Y₂ := _,
    Z := _,
    g₁ := i.f,
    g₂ := 𝟙 _,
    f₁ := I.f,
    f₂ := i.f ≫ I.f,
    h₁ := I.hf,
    h₂ := sieve.downward_closed _ I.hf _,
    w := by simp },
  have := x.condition' RR,
  cases I,
  erw this,
  dsimp [RR],
  simpa,
end

lemma to_plus_eq_mk {X : C} {P : Cᵒᵖ ⥤ D} (x : P.obj (op X)) :
  (J.to_plus_app P).app _ x = mk (meq.mk ⊤ x) :=
begin
  dsimp [mk],
  delta cover.to_multiequalizer,
  simp only [comp_apply],
  congr' 1,
  apply_fun (meq.equiv P ⊤),
  swap, { apply_instance },
  simp only [equiv.apply_symm_apply],
  ext i,
  simpa,
end

lemma eq_mk_iff_exists {X : C} {P : Cᵒᵖ ⥤ D} {S T : J.cover X}
  (x : meq P S) (y : meq P T) : mk x = mk y ↔ (∃ (W : J.cover X) (h1 : W ⟶ S) (h2 : W ⟶ T),
    x.refine h1 = y.refine h2) :=
begin
  split,
  { intros h,
    dsimp [mk] at h,
    obtain ⟨W,h1,h2,hh⟩ :=
      concrete.colimit_exists_of_eq_of_filtered (J.diagram P X) _ _ _ (colimit.is_colimit _) h,
    use [W.unop, h1.unop, h2.unop],
    ext I,
    apply_fun (multiequalizer.ι (W.unop.index P) I) at hh,
    convert hh,
    all_goals {
      dsimp [diagram],
      simp only [← comp_apply, multiequalizer.lift_ι],
      simp only [category.comp_id, meq.equiv_symm_eq_apply],
      cases I, refl } },
  { rintros ⟨S,h1,h2,e⟩,
    dsimp only [mk],
    apply concrete.colimit_eq_of_exists,
    swap, { apply colimit.is_colimit },
    use [(op S), h1.op, h2.op],
    apply concrete.multiequalizer.eq_of_forall_eq _ _ (limit.is_limit _),
    swap, { apply_instance },
    intros i,
    change (multiequalizer.ι (S.index P) _) _ = (multiequalizer.ι (S.index P) _) _,
    apply_fun (λ ee, ee i) at e,
    convert e,
    all_goals {
      dsimp [diagram],
      simp only [← comp_apply, multiequalizer.lift_ι],
      simp,
      cases i, refl } },
end


theorem injective {X : C} (P : Cᵒᵖ ⥤ D) (S : J.cover X)
  (x y : (J.plus_obj P).obj (op X))
  (h : ∀ (I : S.L), (J.plus_obj P).map I.f.op x = (J.plus_obj P).map I.f.op y) :
  x = y :=
begin
  obtain ⟨Sx,x,rfl⟩ := exists_rep x,
  obtain ⟨Sy,y,rfl⟩ := exists_rep y,
  simp only [res_mk_eq_mk_pullback] at h,
  choose W h1 h2 hh using λ (I : S.L), (eq_mk_iff_exists _ _).mp (h I),
  rw eq_mk_iff_exists,
  let B : J.cover X := ⟨sieve.bind S (λ Y f hf, W ⟨_, f, hf⟩),
    J.bind_covering S.condition (λ _ _ _, (W _).condition)⟩,
  use B,
  let ex : B ⟶ Sx := hom_of_le begin
    rintros Y f ⟨Z,e1,e2,he2,he1,hee⟩,
    rw ← hee,
    apply le_of_hom (h1 ⟨_, _, he2⟩),
    exact he1,
  end,
  let ey : B ⟶ Sy := hom_of_le begin
    rintros Y f ⟨Z,e1,e2,he2,he1,hee⟩,
    rw ← hee,
    apply le_of_hom (h2 ⟨_, _, he2⟩),
    exact he1,
  end,
  use [ex, ey],
  ext1,
  choose Z e1 e2 he2 he1 hee using I.hf,
  let IS : S.L := ⟨Z, e2, he2⟩,
  specialize hh IS,
  let IW : (W IS).L := ⟨_, e1, he1⟩,
  apply_fun (λ e, e IW) at hh,
  convert hh,
  { dsimp,
    let Rx : Sx.R := ⟨I.Y, I.Y, I.Y, 𝟙 _, 𝟙 _, I.f, e1 ≫ e2, _, _, by simp [hee]⟩,
    have := x.condition' Rx,
    dsimp [Rx] at this,
    simpa using this },
  { dsimp,
    let Ry : Sy.R := ⟨I.Y, I.Y, I.Y, 𝟙 _, 𝟙 _, I.f, e1 ≫ e2, _, _, by simp [hee]⟩,
    have := y.condition' Ry,
    dsimp [Ry] at this,
    simpa using this },
end

theorem surjective (P : Cᵒᵖ ⥤ D)
  (sep : ∀ (X : C) (S : J.cover X) (x y : P.obj (op X)),
    (∀ I : S.L, P.map I.f.op x = P.map I.f.op y) → x = y)
  (X : C) (S : J.cover X)
  (s : meq (J.plus_obj P) S) :
  ∃ t : (J.plus_obj P).obj (op X), meq.mk S t = s :=
begin
  have inj : ∀ (X : C), function.injective ((J.to_plus_app P).app (op X)),
  { intros X x y h,
    simp only [to_plus_eq_mk] at h,
    rw eq_mk_iff_exists at h,
    obtain ⟨W,h1,h2,hh⟩ := h,
    specialize sep X W,
    apply sep,
    intros I,
    apply_fun (λ e, e I) at hh,
    exact hh },
  choose T t ht using λ I, exists_rep (s I),
  let B : J.cover X := ⟨sieve.bind S (λ Y f hf, T ⟨Y,f,hf⟩),
    J.bind_covering S.condition (λ _ _ _, (T _).condition)⟩,
  choose Z e1 e2 he2 he1 hee using λ I : B.L, I.hf,
  let w : meq P B := ⟨λ I, t ⟨Z I, e2 I, he2 I⟩ ⟨I.Y, e1 I, he1 I⟩, _⟩,
  swap, {
    intros I,
    let I₁ : B.L := ⟨_, I.f₁, I.h₁⟩,
    let I₂ : B.L := ⟨_, I.f₂, I.h₂⟩,
    let IC₁ : S.L := ⟨_, e2 I₁, he2 I₁⟩,
    let IC₂ : S.L := ⟨_, e2 I₂, he2 I₂⟩,
    let ID₁ : (T IC₁).L := ⟨_, e1 I₁, he1 I₁⟩,
    let ID₂ : (T IC₂).L := ⟨_, e1 I₂, he1 I₂⟩,
    change (P.map I.g₁.op) (t IC₁ ID₁) = (P.map I.g₂.op) (t IC₂ ID₂),
    apply inj,
    rw [← comp_apply, ← comp_apply, (J.to_plus_app P).naturality, (J.to_plus_app P).naturality,
      comp_apply, comp_apply],
    rw [@to_plus_apply C _ D _ J _ _ _ _ _ _ _ _ (T IC₁) (t IC₁) ID₁,
      @to_plus_apply C _ D _ J _ _ _ _ _ _ _ _ (T IC₂) (t IC₂) ID₂,
      ← ht, ← ht, ← comp_apply, ← comp_apply, ← (J.plus_obj P).map_comp,
      ← (J.plus_obj P).map_comp, ← op_comp, ← op_comp],
    let IR : S.R :=
    { Y₁ := _,
      Y₂ := _,
      Z := _,
      g₁ := I.g₁ ≫ ID₁.f,
      g₂ := I.g₂ ≫ ID₂.f,
      f₁ := e2 I₁,
      f₂ := e2 I₂,
      h₁ := he2 _,
      h₂ := he2 _,
      w := _ },
    swap, { dsimp [ID₁, ID₂], simp_rw [category.assoc, hee], exact I.w },
    exact s.condition' IR },
  use mk w,
  ext I,
  rw ht,
  dsimp only [meq.mk],
  change (J.plus_obj P).map _ _ = _,
  erw [res_mk_eq_mk_pullback],
  apply injective P (T I),
  intros II,
  simp only [res_mk_eq_mk_pullback],
  rw eq_mk_iff_exists,
  use (J.pullback II.f).obj (T I),
  let e0 : (J.pullback II.f).obj (T I) ⟶ (J.pullback II.f).obj ((J.pullback I.f).obj B) :=
    hom_of_le begin
      rintros Y f hf,
      fapply sieve.le_pullback_bind,
      { exact I.hf },
      { cases I,
        exact hf },
    end,
  use [e0, 𝟙 _],
  ext IV,
  dsimp only [meq.refine_apply],
  dsimp only [meq.pullback_apply],
  dsimp [w],
  let IA : B.L := {Y := IV.Y, f := (IV.f ≫ II.f) ≫ I.f, hf := _},
  swap, {
    refine ⟨I.Y,_,_,I.hf,_,rfl⟩,
    apply sieve.downward_closed,
    dsimp,
    convert II.hf,
    cases I, refl },
  let IB : S.L := {Y := Z IA, f := e2 IA, hf := _},
  swap, { apply he2, },
  let IC : (T IB).L := {Y := IV.Y, f := e1 IA, hf := _},
  swap, { apply he1, },
  let ID : (T I).L := {Y := IV.Y, f := IV.f ≫ II.f, hf := _},
  swap, { apply sieve.downward_closed, apply II.hf, },
  change t IB IC = t I ID,
  apply inj IV.Y,
  erw @to_plus_apply C _ D _ J _ _ _ _ _ _ _ _ (T I) (t I) ID,
  erw @to_plus_apply C _ D _ J _ _ _ _ _ _ _ _ (T IB) (t IB) IC,
  rw [← ht, ← ht],
  dsimp only,
  let IR : S.R :=
  { Y₁ := _,
    Y₂ := _,
    Z := IV.Y,
    g₁ := e1 IA,
    g₂ := IV.f ≫ II.f,
    f₁ := e2 IA,
    f₂ := I.f,
    h₁ := he2 _,
    h₂ := I.hf,
    w := _ },
  swap, { rw hee },
  convert s.condition' IR,
  cases I, refl,
end .

theorem is_sheaf_of_sep (P : Cᵒᵖ ⥤ D)
  (sep : ∀ (X : C) (S : J.cover X) (x y : P.obj (op X)),
    (∀ I : S.L, P.map I.f.op x = P.map I.f.op y) → x = y) :
  presheaf.is_sheaf J (J.plus_obj P) :=
begin
  rw presheaf.is_sheaf_iff_multiequalizer,
  intros X S,
  apply is_iso_of_reflects_iso _ (forget D),
  rw is_iso_iff_bijective,
  split,
  { intros x y h,
    apply injective P S _ _,
    intros I,
    apply_fun (meq.equiv _ _) at h,
    apply_fun (λ e, e I) at h,
    convert h,
    { rw meq.equiv_apply,
      erw [← comp_apply, multiequalizer.lift_ι] },
    { rw meq.equiv_apply,
      erw [← comp_apply, multiequalizer.lift_ι] } },
  { rintros (x : (multiequalizer (S.index _) : D)),
    obtain ⟨t,ht⟩ := surjective P sep X S (meq.equiv _ _ x),
    use t,
    apply_fun meq.equiv _ _,
    swap, { apply_instance },
    swap, { apply_instance },
    swap, { apply_instance },
    swap, { apply_instance },
    rw ← ht,
    ext i,
    dsimp,
    erw [← comp_apply, multiequalizer.lift_ι],
    refl }
end

end plus
end category_theory.grothendieck_topology
