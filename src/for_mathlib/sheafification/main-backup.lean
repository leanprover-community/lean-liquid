import category_theory.limits.concrete_category
import for_mathlib.sheafification.plus_sheaf_condition
import for_mathlib.concrete_filtered
import for_mathlib.concrete_multiequalizer

namespace category_theory.grothendieck_topology

open category_theory
open category_theory.limits
open opposite

universes w v u
variables {C : Type u} [category.{v} C] {D : Type w}
  [category.{max v u} D] (J : grothendieck_topology C)

variables [has_limits D] [has_colimits D]
variables [concrete_category.{max v u} D]
variables [preserves_limits (forget D)]
variables [∀ (X : C), preserves_colimits_of_shape (J.cover X)ᵒᵖ (forget D)]
variables [reflects_isomorphisms (forget D)]

local attribute [instance]
  concrete_category.has_coe_to_sort concrete_category.has_coe_to_fun

namespace plus

abbreviation meq {X : C} (P : Cᵒᵖ ⥤ D) (S : J.cover X) :=
{ x : Π (I : S.L), P.obj (op I.Y) // ∀ (I : S.R),
    P.map I.g₁.op (x ⟨_, I.f₁, I.h₁⟩) = P.map I.g₂.op (x ⟨_, I.f₂, I.h₂⟩) }

noncomputable
def meq_equiv {X : C} (P : Cᵒᵖ ⥤ D) (S : J.cover X) :
  (multiequalizer (S.index P) : D) ≃ meq J P S :=
{ to_fun := λ x, ⟨λ I, multiequalizer.ι (S.index P) I x, sorry⟩,
  inv_fun := sorry,
  left_inv := sorry,
  right_inv := sorry }

@[simp]
lemma meq_equiv_ι {X : C} (P : Cᵒᵖ ⥤ D) (S : J.cover X)
  (x : multiequalizer (S.index P)) (I : S.L) :
  (meq_equiv J P S x).1 I = multiequalizer.ι (S.index P) I x := sorry

def to_meq {X : C} (P : Cᵒᵖ ⥤ D) (S : J.cover X) (x : P.obj (op X)) : meq J P S :=
⟨λ I, P.map I.f.op x, begin
  intros I,
  dsimp,
  simp only [← comp_apply, ← P.map_comp, ← op_comp, I.w],
end⟩

def map_to_meq {Y X : C} (P : Cᵒᵖ ⥤ D) (S : J.cover X)
  (x : P.obj (op X)) (I : S.L) (f : Y ⟶ I.Y) :
  P.map f.op ((to_meq J P _ x).1 I) = (to_meq J P S x).1 ⟨_, f ≫ I.f,
    sieve.downward_closed _ I.hf _⟩ := by { dsimp [to_meq], simp }

@[simp]
lemma meq_equiv_lift {W} {X : C} (P : Cᵒᵖ ⥤ D) (S : J.cover X)
  (k : Π (I : S.L), W ⟶ P.obj (op I.Y))
  (h : ∀ (I : S.R), k ⟨_, I.f₁, I.h₁⟩ ≫ P.map I.g₁.op = k ⟨_, I.f₂, I.h₂⟩ ≫ P.map I.g₂.op)
  (x : W) :
  meq_equiv J P S ((multiequalizer.lift (S.index P) W k h) x) =
  ⟨λ I, k I x, begin
    intros I,
    simp only [← comp_apply, h],
  end⟩ := sorry

lemma exists_rep {P : Cᵒᵖ ⥤ D} (X : C) (x : (J.plus_obj P).obj (op X)) :
  ∃ (S : J.cover X) (y : multiequalizer (S.index P)),
    colimit.ι (J.diagram P X) (op S) y = x :=
begin
  obtain ⟨S,y,t⟩ := concrete.is_colimit_exists_rep (J.diagram P X) (colimit.is_colimit _) x,
  use [S.unop, y, t],
end

@[simp]
lemma rep_res {P : Cᵒᵖ ⥤ D} (X Y : C) (f : Y ⟶ X)
  (S : J.cover X) (x : multiequalizer (S.index P)) :
  (J.plus_obj P).map f.op (colimit.ι (J.diagram P X) (op S) x) =
  colimit.ι (J.diagram P Y) (op ((J.pullback f).obj S))
    ((J.diagram_pullback P f).app (op S) x) :=
begin
  dsimp [plus_obj],
  simp_rw ← comp_apply,
  congr' 1,
  simpa,
end

lemma exists_of_rep_eq (P : Cᵒᵖ ⥤ D) (X : C) (S T : J.cover X)
  (x : (J.diagram P X).obj (op S)) (y : (J.diagram P X).obj (op T))
  (h : colimit.ι (J.diagram P X) (op S) x = colimit.ι (J.diagram P X) (op T) y) :
  ∃ (W : J.cover X) (f : W ⟶ S) (g : W ⟶ T),
    (J.diagram P X).map f.op x = (J.diagram P X).map g.op y :=
begin
  have := concrete.colimit_exists_of_eq_of_filtered (J.diagram P X) x y _ (colimit.is_colimit _) h,
  obtain ⟨W,f,g,hh⟩ := this,
  use [W.unop, f.unop, g.unop, hh],
end

lemma rep_eq_of_exists (P : Cᵒᵖ ⥤ D) (X : C) (S T : J.cover X)
  (x : (J.diagram P X).obj (op S)) (y : (J.diagram P X).obj (op T))
  (h : ∃ W (f : W ⟶ S) (g : W ⟶ T), (J.diagram P X).map f.op x = (J.diagram P X).map g.op y) :
  colimit.ι (J.diagram P X) (op S) x = colimit.ι (J.diagram P X) (op T) y :=
begin
  apply concrete.colimit_eq_of_exists,
  obtain ⟨W,f,g,h⟩ := h,
  use [(op W), f.op, g.op, h],
  exact colimit.is_colimit _,
end

theorem injective (P : Cᵒᵖ ⥤ D) (X : C) (S : J.cover X)
  (x y : (J.plus_obj P).obj (op X))
  (h : ∀ (I : S.L), (J.plus_obj P).map I.f.op x = (J.plus_obj P).map I.f.op y) :
  x = y :=
begin
  /-
  obtain ⟨Sx,x,rfl⟩ := exists_rep _ _ x,
  obtain ⟨Sy,y,rfl⟩ := exists_rep _ _ y,
  apply rep_eq_of_exists,
  let T := S ⊓ Sx ⊓ Sy,
  let eS : T ⟶ S := hom_of_le (le_trans inf_le_left inf_le_left),
  let ex : T ⟶ Sx := hom_of_le (le_trans inf_le_left inf_le_right),
  let ey : T ⟶ Sy := hom_of_le inf_le_right,
  simp only [rep_res] at h,
  replace h := λ I, exists_of_rep_eq J P _ _ _ _ _ (h I),
  choose W ff gg hh using h,
  let B : J.cover X := ⟨sieve.bind S (λ Y f hf, W ⟨Y,f,hf⟩),
    J.bind_covering S.condition (λ _ _ _, (W _).condition)⟩,
  use B,
  let eBx : B ⟶ Sx := hom_of_le begin
    rintros Y f ⟨Z,h1,h2,h3,h4,h5⟩,
    rw ← h5,
    apply le_of_hom (ff ⟨Z,h2,h3⟩),
    exact h4,
  end,
  let eBy : B ⟶ Sy := hom_of_le begin
    rintros Y f ⟨Z,h1,h2,h3,h4,h5⟩,
    rw ← h5,
    apply le_of_hom (gg ⟨Z,h2,h3⟩),
    exact h4,
  end,
  use [eBx, eBy],
  dsimp [diagram],
  apply_fun meq_equiv J P B,
  simp,
  ext ⟨Y,f,hf⟩,
  choose Z e1 e2 h1 h2 h3 using hf,
  let II : S.L := ⟨Z, e2, h1⟩,
  specialize hh II,
  apply_fun meq_equiv J P _ at hh,
  simp at hh,
  dsimp at hh,
  simp [← comp_apply] at hh,
  let III : (W II).L := ⟨Y, e1, h2⟩,
  apply_fun (λ e, e III) at hh,
  convert hh,
  { dsimp [cover.map_L],
    sorry },
  { dsimp [cover.map_L],
    sorry },
  -/
  sorry
end

theorem surjective (P : Cᵒᵖ ⥤ D)
  (sep : ∀ (X : C) (S : J.cover X) (x y : P.obj (op X)),
    (∀ (I : S.L), P.map I.f.op x = P.map I.f.op y) → x = y)
  (X : C) (S : J.cover X)
  (s : { x : Π (I : S.L), (J.plus_obj P).obj (op I.Y) //
    ∀ (I : S.R), (J.plus_obj P).map I.g₁.op (x ⟨_, I.f₁, I.h₁⟩) =
      (J.plus_obj P).map I.g₂.op (x ⟨_, I.f₂, I.h₂⟩) }) :
  ∃ t : (J.plus_obj P).obj (op X), s = to_meq J (J.plus_obj P) S t :=
begin
  cases s with s hs,
  choose W w hw using λ I : S.L, exists_rep J I.Y (s I),
  let w' := λ (I : S.L) (II : (W I).L), (meq_equiv J _ _ (w I)).1 II,
  have hw' : ∀ (I : S.L) (II : (W I).R),
    P.map II.g₁.op (w' I ⟨_, II.f₁, II.h₁⟩) = P.map II.g₂.op (w' I ⟨_, II.f₂, II.h₂⟩) :=
    λ I II, (meq_equiv J _ _ (w I)).2 II,
  let B : J.cover X := ⟨sieve.bind S (λ Y f hf, W ⟨_, f, hf⟩),
    J.bind_covering S.condition (λ _ _ _, (W _).condition)⟩,
  choose Z e1 e2 h1 h2 h3 using (λ I : B.L, I.hf),
  let t : { x : Π (I : B.L), P.obj (op I.Y) // ∀ (I : B.R),
    P.map I.g₁.op (x ⟨_, I.f₁, I.h₁⟩) = P.map I.g₂.op (x ⟨_, I.f₂, I.h₂⟩) } :=
    ⟨λ I, w' ⟨_, e2 I, h1 I⟩ ⟨_, e1 I, h2 I⟩, _⟩,
  swap, { sorry },
  let t' := (meq_equiv J P _).symm t,
  use colimit.ι (J.diagram P X) (op B) t',
  ext I : 2,
  dsimp,
  apply injective J P I.Y (W I),
  intros II,
  have : ((J.plus_obj P).map II.f.op) (s I) = s ⟨II.Y, II.f ≫ I.f,
    sieve.downward_closed _ I.hf _⟩,
  { let IR : S.R := ⟨I.Y, II.Y, II.Y, II.f, 𝟙 _, I.f, II.f ≫ I.f, I.hf,
      sieve.downward_closed _ I.hf _, by simp⟩,
    specialize hs IR,
    dsimp only [IR, op_id] at hs,
    rw [(J.plus_obj P).map_id, id_apply] at hs,
    convert hs,
    cases I, refl },
  rw this, clear this,
  let III : B.L := ⟨II.Y, II.f ≫ I.f, _⟩,
  swap, {
    use [I.Y, II.f, I.f, I.hf],
    refine ⟨_, rfl⟩,
    dsimp,
    cases I,
    exact II.hf },
  have : ((J.plus_obj P).map II.f.op)
    ((to_meq J (J.plus_obj P) S ((colimit.ι (J.diagram P X) (op B)) t')).1 I) =
      (J.to_plus_app P).app _ (t.1 III),
  { sorry },
  erw this, clear this,
  rw ← hw,
  dsimp [t, w'],
  delta cover.to_multiequalizer,
  simp only [comp_apply],
  let I' : S.L := ⟨II.Y, II.f ≫ I.f, sieve.downward_closed _ I.hf _⟩,
  let e' : W I' ⟶ ⊤ := hom_of_le sorry,
  rw [← colimit.w _ e'.op, comp_apply],
  congr' 1,
  apply_fun meq_equiv J P _,
  ext II' : 2,
  simp,
  simp only [← comp_apply],
  dsimp only [meq_equiv],
  dsimp,
  simp,
  dsimp [multifork.of_ι],
  simp only [← comp_apply],
  simp,
  simp only [← comp_apply],
  sorry,
end

/-
theorem injective (P : Cᵒᵖ ⥤ D) (X : C) (S : J.cover X)
  (x y : (J.plus_obj P).obj (op X))
  (h : ∀ (I : S.L), (J.plus_obj P).map I.f.op x = (J.plus_obj P).map I.f.op y) :
  x = y :=
begin
  obtain ⟨Sx,x,rfl⟩ := exists_rep _ _ x,
  obtain ⟨Sy,y,rfl⟩ := exists_rep _ _ y,
  let T := S ⊓ Sx ⊓ Sy,
  let eS : T ⟶ S := hom_of_le (le_trans inf_le_left inf_le_left),
  let ex : T ⟶ Sx := hom_of_le (le_trans inf_le_left inf_le_right),
  let ey : T ⟶ Sy := hom_of_le inf_le_right,
  simp only [rep_res] at h,
  replace h := λ I, exists_of_rep_eq J P _ _ _ _ _ (h I),
  choose W ff gg hh using h,
  apply rep_eq_of_exists,
  let B : J.cover X := ⟨sieve.bind S (λ Y f hf, W ⟨Y,f,hf⟩),
    J.bind_covering S.condition (λ _ _ _, (W _).condition)⟩,
  use B,
  let eBx : B ⟶ Sx := hom_of_le begin
    rintros Y f ⟨Z,h1,h2,h3,h4,h5⟩,
    rw ← h5,
    apply le_of_hom (ff ⟨Z,h2,h3⟩),
    exact h4,
  end,
  let eBy : B ⟶ Sy := hom_of_le begin
    rintros Y f ⟨Z,h1,h2,h3,h4,h5⟩,
    rw ← h5,
    apply le_of_hom (gg ⟨Z,h2,h3⟩),
    exact h4,
  end,
  use [eBx, eBy],
  apply concrete.multiequalizer.eq_of_forall_eq _ _ (limit.is_limit _),
  swap, apply_instance,
  rintros ⟨Y,π,Z,e1,e2,h1,h2,h3⟩,
  dsimp at h2,
  specialize hh ⟨_, e2, h1⟩,
  apply_fun multiequalizer.ι ((W ⟨_, e2, h1⟩).index P) ⟨_, e1, h2⟩ at hh,
  convert hh using 1,
  all_goals { dsimp,
    simp only [← comp_apply],
    congr' 1,
    simp only [multiequalizer.lift_ι, category.comp_id, category.assoc],
    dsimp [cover.map_L],
    congr,
    exact h3.symm },
end .

noncomputable def pullback_multiequalizer (X : C) (P : Cᵒᵖ ⥤ D) (S : J.cover X)
  (s : multiequalizer (S.index P)) (I : S.L) :
  (multiequalizer (((J.pullback I.f).obj S).index P) : D) :=
concrete.multiequalizer.mk _ _ (limit.is_limit _)
  (λ II, multiequalizer.ι (S.index P) ⟨II.Y, II.f ≫ I.f, II.hf⟩ s)
begin
  intros II,
  simp only [← comp_apply],
  congr' 1,
  apply multiequalizer.condition (S.index P)
    ⟨II.Y₁, II.Y₂, II.Z, II.g₁, II.g₂, II.f₁ ≫ I.f, II.f₂ ≫ I.f, II.h₁, II.h₂,
      by simp [reassoc_of II.w]⟩,
end

theorem surjective (P : Cᵒᵖ ⥤ D)
  (sep : ∀ (X : C) (S : J.cover X) (x y : P.obj (op X)),
    (∀ I : S.L, P.map I.f.op x = P.map I.f.op y) → x = y)
  (X : C) (S : J.cover X)
  (s : multiequalizer (S.index (J.plus_obj P))) :
  ∃ (t : (J.plus_obj P).obj (op X)),
    S.to_multiequalizer (J.plus_obj P) t = s :=
begin
  let SI := (S.index (J.plus_obj P)),

  -- The local sections associated to s.
  let t : Π (I : S.L), (J.plus_obj P).obj (op I.Y) :=
    λ I, (multiequalizer.ι SI I) s,
  -- The compatibility among the (t I)'s,
  have ht : ∀ (I : S.R),
    (J.plus_obj P).map I.g₁.op (t (SI.fst_to I)) =
    (J.plus_obj P).map I.g₂.op (t (SI.snd_to I)),
  { -- this is the multiequalizer condition arising from the original section s.
    sorry },
  have W_aux : ∀ (I : S.L), ∃ (W : J.cover I.Y) (w : (J.diagram P I.Y).obj (op W)),
    colimit.ι (J.diagram P I.Y) (op W) w = t I,
  { intros I,
    apply exists_rep },
  -- W I is the cover of I.Y and w are local sections over W I defining t I.
  choose W w hw using W_aux,
  dsimp only [diagram, unop_op] at w,
  -- The local sections associated to w.
  let ws : Π (I : S.L) (II : (W I).L), P.obj (op II.Y) :=
    λ I II, multiequalizer.ι ((W I).index P) II (w I),
  -- compatibility among the ws's.
  have hws : ∀ (I : S.L) (II : (W I).R),
    P.map II.g₁.op (ws I (((W I).index P).fst_to II)) =
    P.map II.g₂.op (ws I (((W I).index P).snd_to II)),
  { -- again, just the multieq condition from w.
    sorry
  },

  -- the cover over which we need to define the local sections to obtain a global section
  let B : J.cover X := ⟨sieve.bind S (λ Y f hf, W ⟨Y,f,hf⟩),
    J.bind_covering S.condition (λ _ _ _, (W _).condition)⟩,
  have B_aux : ∀ (I : B.L), B I.f := λ I, I.hf,
  choose Z e1 e2 h1 h2 h3 using B_aux,
  let ts : (multiequalizer (B.index P) : D) :=
    concrete.multiequalizer.mk _ _ (limit.is_limit _)
      (λ I, ws ⟨Z I, e2 I, h1 I⟩ ⟨I.Y, e1 I, h2 I⟩) _,
  swap,
  { -- this is the compatibility of the ws...
    -- this might be hard... we'll see.
    sorry },
  use colimit.ι (J.diagram P X) (op B) ts,

  -- Now let's prove that it actually maps to the original multisection s.
  apply concrete.multiequalizer.eq_of_forall_eq _ _ (limit.is_limit _),
  swap, apply_instance,

  rintros (I : S.L),
  simp_rw [← comp_apply, category.assoc],
  erw multiequalizer.lift_ι,
  dsimp only [multiequalizer.multifork_ι],
  change _ = t _,

  apply injective J P _ (W I),
  intros II,
  rw [← comp_apply, category.assoc],
  let III : B.L := ⟨II.Y, II.f ≫ I.f, I.Y, II.f, I.f, I.hf, _, rfl⟩,
  swap, { dsimp, convert II.hf, cases I, refl },

  have : ((J.plus_obj P).map II.f.op) (t I) =
    colimit.ι (J.diagram P II.Y) (op $ (J.pullback II.f).obj (W I))
    (pullback_multiequalizer J I.Y P (W I) (w I) II),
  { sorry },
  rw this,
  --let ts' : P.obj (op III.Y) := ((multiequalizer.ι (B.index P) III) ts),
  have : (colimit.ι (J.diagram P X) (op B) ≫
    (J.plus_obj P).map I.f.op ≫ (J.plus_obj P).map II.f.op) ts =
    (to_plus_app J P).app (op III.Y) (multiequalizer.ι (B.index P) III ts),
  { sorry
    /-
    dsimp,
    simp_rw [← comp_apply],
    congr' 1,
    simp only [grothendieck_topology.diagram_pullback_app, colimit.ι_pre_assoc,
      colimit.ι_pre, ι_colim_map_assoc, category.assoc],
    let et : (J.pullback II.f).obj ((J.pullback I.f).obj B) ⟶ ⊤ := hom_of_le sorry,
    simp_rw [← colimit.w (J.diagram P II.Y) et.op, ← category.assoc],
    congr' 1,
    dsimp,
    simp only [category.comp_id, category.assoc],
    delta cover.to_multiequalizer,
    ext,
    dsimp,
    simp only [multiequalizer.lift_ι, category.assoc],
    dsimp [cover.map_L],
    let IB : (B.index P).R := ⟨a.Y, III.Y, a.Y, 𝟙 _, a.f, a.f ≫ III.f,
      III.f, sieve.downward_closed _ III.hf _, III.hf, by simp⟩,
    have := multiequalizer.condition (B.index P) IB,
    convert this using 1,
    dsimp [cover.index, IB],
    rw [P.map_id (op a.Y), category.comp_id],
    congr' 2, rw category.assoc
    -/
  },
  rw this, clear this,
  erw concrete.multiequalizer.mk_ι,
  dsimp [ws],
  delta cover.to_multiequalizer,
  dsimp [pullback_multiequalizer],
  simp,
  let ees : ((J.pullback II.f).obj (W I)) ⟶ ⊤ := hom_of_le sorry,
  rw ← colimit.w _ ees.op,
  simp only [comp_apply],
  congr' 1,
  apply concrete.multiequalizer.eq_of_forall_eq _ _ (limit.is_limit _),
  swap, apply_instance,
  intros tt,
  dsimp,
  simp,
  simp only [← comp_apply],
  erw concrete.multiequalizer.mk_ι,
  dsimp [multifork.of_ι],
  simp,
  simp only [← comp_apply],
  dsimp [cover.map_L],
  let IR : (W I).R := ⟨tt.Y, II.Y, tt.Y, 𝟙 _, tt.f, tt.f ≫ II.f, II.f,
    sieve.downward_closed _ II.hf _, II.hf, by simp⟩,
  have ttt := multiequalizer.condition ((W I).index P) IR,
  dsimp [cover.index] at ttt,
  erw [P.map_id, category.comp_id] at ttt,
  change (multiequalizer.ι ((W I).index P) _ ≫ _) _ = _,
  erw ttt,

  /-
  let wz : (J.diagram P III.Y).obj (op ((J.pullback II.f).obj (W I))) :=
    concrete.multiequalizer.mk _ _ (limit.is_limit _)
      (λ tt, ws I ⟨tt.Y, tt.f ≫ II.f, tt.hf⟩) _,
  swap,
  { sorry },
  have : ((J.to_plus_app P).app (op III.Y))
    (ws ⟨Z III, e2 III, h1 III⟩ ⟨III.Y, e1 III, h2 III⟩) =
    colimit.ι (J.diagram P III.Y) (op $ (J.pullback II.f).obj (W _)) wz, sorry,
  rw this,
  dsimp only [wz],
  -/

  sorry,
end

-/

end plus

/-
theorem injective_to_plus_app (P : Cᵒᵖ ⥤ D) (X : C) :
  function.injective ((J.to_plus_app P).app (op X)) := sorry

lemma plus_exists_rep (P : Cᵒᵖ ⥤ D) (X : C) (x : (plus_obj J P).obj (op X)) :
  ∃ (S : J.cover X) (y : (J.diagram P X).obj (op S)),
    colimit.ι (J.diagram P X) (op S) y = x :=
begin
  obtain ⟨S,y,t⟩ := concrete.is_colimit_exists_rep (J.diagram P X) (colimit.is_colimit _) x,
  use [S.unop, y, t],
end

lemma plus_rep_eq (P : Cᵒᵖ ⥤ D) (X : C) (S T : J.cover X)
  (x : (J.diagram P X).obj (op S)) (y : (J.diagram P X).obj (op T))
  (h : colimit.ι (J.diagram P X) (op S) x = colimit.ι (J.diagram P X) (op T) y) :
  ∃ (W : J.cover X) (f : W ⟶ S) (g : W ⟶ T),
    (J.diagram P X).map f.op x = (J.diagram P X).map g.op y :=
begin
  have := concrete.colimit_exists_of_eq_of_filtered (J.diagram P X) x y _ (colimit.is_colimit _) h,
  obtain ⟨W,f,g,hh⟩ := this,
  use [W.unop, f.unop, g.unop, hh],
end

lemma plus_rep_eq_of_exists (P : Cᵒᵖ ⥤ D) (X : C) (S T : J.cover X)
  (x : (J.diagram P X).obj (op S)) (y : (J.diagram P X).obj (op T))
  (h : ∃ W (f : W ⟶ S) (g : W ⟶ T), (J.diagram P X).map f.op x = (J.diagram P X).map g.op y) :
  colimit.ι (J.diagram P X) (op S) x = colimit.ι (J.diagram P X) (op T) y :=
begin
  apply concrete.colimit_eq_of_exists,
  obtain ⟨W,f,g,h⟩ := h,
  use [(op W), f.op, g.op, h],
  exact colimit.is_colimit _,
end

noncomputable def plus_rep_res (P : Cᵒᵖ ⥤ D) (X : C) (S : J.cover X) (I : (S.index P).L) :
  (J.diagram P X).obj (op S) ⟶ P.obj (op I.Y) :=
multiequalizer.ι _ _

lemma plus_rep_eq_res (P : Cᵒᵖ ⥤ D) (X : C) (S : J.cover X) (x y : (J.diagram P X).obj (op S))
  (h : ∀ (I : (S.index P).L), plus_rep_res J P X S I x = plus_rep_res J P X S I y) : x = y :=
begin
  apply concrete.multiequalizer.eq_of_forall_eq _ _ (limit.is_limit _),
  exact h,
  apply_instance
end

lemma plus_rep_res_map (P : Cᵒᵖ ⥤ D) (X : C) (S T : J.cover X) (e : S ⟶ T)
  (x : (J.diagram P X).obj (op T)) (I : (S.index P).L) :
  (J.diagram P X).map e.op ≫ plus_rep_res J P X S I =
  plus_rep_res J P X T (cover.map_L e I) :=
begin
  dsimp [plus_rep_res],
  simp,
end

theorem plus_ext  (P : Cᵒᵖ ⥤ D)
  (X : C) (S : J.cover X) (x y : (plus_obj J P).obj (op X))
  (h : ∀ (I : (S.index P).L),
    (plus_obj J P).map I.f.op x = (plus_obj J P).map I.f.op y) : x = y :=
begin
  obtain ⟨Sx,x,rfl⟩ := plus_exists_rep J P X x,
  obtain ⟨Sy,y,rfl⟩ := plus_exists_rep J P X y,
  let W := S ⊓ Sx ⊓ Sy,
  let eS : W ⟶ S := hom_of_le (le_trans inf_le_left inf_le_left),
  let ex : W ⟶ Sx := hom_of_le (le_trans inf_le_left inf_le_right),
  let ey : W ⟶ Sy := hom_of_le inf_le_right,
  let xx := (J.diagram P X).map ex.op x,
  let yy := (J.diagram P X).map ey.op y,
  dsimp only [plus_obj] at h,
  simp only [← comp_apply] at h,
  simp only [colimit.ι_pre, ι_colim_map_assoc, comp_apply] at h,
  dsimp only [category_theory.functor.op_obj] at h,
  replace h := λ (I : (S.index P).L), plus_rep_eq J P _ _ _ _ _ (h I),
  dsimp only [unop_op, quiver.hom.unop_op] at h,
  let Ws : Π (I : (S.index P).L), J.cover I.Y :=
    λ I, (h I).some,
  let fs : Π (I : (S.index P).L), Ws I ⟶ (J.pullback I.f).obj Sx :=
    λ I, (h I).some_spec.some,
  let gs : Π (I : (S.index P).L), Ws I ⟶ (J.pullback I.f).obj Sy :=
    λ I, (h I).some_spec.some_spec.some,
  have hhs : ∀ (I : (S.index P).L),
    (J.diagram P I.Y).map (fs I).op ((J.diagram_pullback P I.f).app (op Sx) x) =
    (J.diagram P I.Y).map (gs I).op ((J.diagram_pullback P I.f).app (op Sy) y) :=
    λ I, (h I).some_spec.some_spec.some_spec,
  apply plus_rep_eq_of_exists,
  let WW : J.cover X := ⟨sieve.bind S (λ Y f hf, Ws ⟨Y,f,hf⟩),
    J.bind_covering S.condition (λ Y f hf, (Ws _).condition)⟩,
  use WW,
  let ees : Π (I : (S.index P).L), Ws I ⟶ (J.pullback I.f).obj WW :=
    λ I, hom_of_le $ begin
      dsimp [pullback],
      intros Y f hf,
      apply sieve.le_pullback_bind _ _ _ I.hf,
      cases I, exact hf,
    end,
  let ff : WW ⟶ Sx := hom_of_le (λ Y f hf, begin
    obtain ⟨Z,g,e,he,h1,h2⟩ := hf,
    dsimp at h1,
    rw ← h2,
    apply le_of_hom (fs ⟨Z,e,he⟩),
    exact h1
  end),
  let gg : WW ⟶ Sy := hom_of_le (λ Y f hf, begin
    obtain ⟨Z,g,e,he,h1,h2⟩ := hf,
    dsimp at h1,
    rw ← h2,
    apply le_of_hom (gs ⟨Z,e,he⟩),
    exact h1,
  end),
  use [ff, gg],
  apply plus_rep_eq_res,
  rintros ⟨Y,f,⟨Z,g,e,he,h1,rfl⟩⟩,
  dsimp at h1,
  specialize hhs ⟨Z,e,he⟩,
  let WsI : ((Ws ⟨Z,e,he⟩).index P).L := ⟨_,g,h1⟩,
  apply_fun plus_rep_res J P Z (Ws ⟨Z,e,he⟩) WsI at hhs,
  convert hhs using 1,
  { dsimp [plus_rep_res],
    simp,
    dsimp [multifork.of_ι],
    simp only [← comp_apply],
    congr' 1,
    simpa },
  { dsimp [plus_rep_res],
    simp,
    dsimp [multifork.of_ι],
    simp only [← comp_apply],
    congr' 1,
    simpa }
end

theorem is_sheaf_of_ext
  (P : Cᵒᵖ ⥤ D) (h : ∀ (X : C) (S : J.cover X) (x y : P.obj (op X))
    (hh : ∀ (I : (S.index P).L), P.map I.f.op x = P.map I.f.op y), x = y) :
  presheaf.is_sheaf J (J.plus_obj P) :=
begin
  rw presheaf.is_sheaf_iff_multiequalizer,
  intros X S,
  suffices : is_iso ((forget D).map $ S.to_multiequalizer (J.plus_obj P)),
  { apply is_iso_of_reflects_iso _ (forget D), exact this, },
  rw is_iso_iff_bijective,
  dsimp,
  split,
  {
    /-
    intros x y hh,
    apply plus_ext _ _ _ S,
    any_goals { apply_instance },
    intros I,
    apply_fun multiequalizer.ι (S.index (J.plus_obj P)) I at hh,
    convert hh using 1,
    all_goals { dsimp,
      simp_rw ← comp_apply, congr' 1,
      simpa }
    -/
    sorry
  },
  { let Plus := J.plus_obj P,
    intros b,
    -- Local sections which we need to glue.
    let s : Π (I : (S.index Plus).L), Plus.obj (op I.Y) :=
      λ I, multiequalizer.ι (S.index Plus) I b,
    -- the condition that should allow us to glue.
    have hs : ∀ (I : (S.index Plus).R), Plus.map I.g₁.op (s ((S.index Plus).fst_to I)) =
      Plus.map I.g₂.op (s ((S.index Plus).snd_to I)), sorry,
    -----
    have T_aux : Π (I : (S.index Plus).L),
      ∃ (T : J.cover I.Y) (y : (J.diagram P I.Y).obj (op T)),
        (colimit.ι (J.diagram P I.Y) (op T)) y = s I,
    { intros I, apply plus_exists_rep },
    -- For each index (I : (S.index Plus).L), choose a cover for which
    -- s I is defined by some local sections from P.
    let T : Π (I : (S.index Plus).L), J.cover I.Y := λ I, (T_aux I).some,
    -- for each such T, the element defining s I,
    let t : Π (I : (S.index Plus).L), (J.diagram P I.Y).obj (op (T I)) :=
      λ I, (T_aux I).some_spec.some,
    -- and the condition about t...
    have ht : ∀ (I : (S.index Plus).L),
      (colimit.ι (J.diagram P I.Y)) (op (T I)) (t I) = s I :=
      λ I, (T_aux I).some_spec.some_spec,

    -- the local sections defining the t's
    let ts : Π (I : (S.index Plus).L) (II : ((T I).index P).L),
      P.obj (op II.Y) := λ I II,
      multiequalizer.ι ((T I).index P) _ (t I),
    -- the compatibility among the ts
    have hts : ∀ (I : (S.index Plus).L) (II : ((T I).index P).R),
      P.map II.g₁.op (ts I (((T I).index P).fst_to II)) =
      P.map II.g₂.op (ts I (((T I).index P).snd_to II)), sorry,

    -- Now we combine the T I into a single cover...
    let W : J.cover X := ⟨sieve.bind S (λ Y f hf, T ⟨Y,f,hf⟩),
      J.bind_covering S.condition (λ Y f hf, (T _).condition)⟩,

    /-
    let ι : W ⟶ S := hom_of_le begin
      rintros Y f ⟨Z,g,e,h1,h2,h3⟩,
      rw ← h3,
      dsimp at h2,
      apply sieve.downward_closed,
      exact h1,
    end,
    -/

    let ZZ : (W.index P).L → C := λ I, I.hf.some,
    let gg : Π (I : (W.index P).L), I.Y ⟶ ZZ I :=
      λ I, I.hf.some_spec.some,
    let ee : Π (I : (W.index P).L), ZZ I ⟶ X :=
      λ I, I.hf.some_spec.some_spec.some,
    have hee : ∀ (I : (W.index P).L), S (ee I) :=
      λ I, I.hf.some_spec.some_spec.some_spec.some,
    let ι : (W.index P).L → (S.index P).L := λ I, ⟨_, ee I, hee I⟩,
    have hgg : ∀ (I : (W.index P).L), (T (ι I)) (gg I) :=
      λ I, I.hf.some_spec.some_spec.some_spec.some_spec.1,
    have hffggee : ∀ (I : (W.index P).L), I.f = gg I ≫ ee I :=
      λ I, I.hf.some_spec.some_spec.some_spec.some_spec.2.symm,
    let δ : Π (I : (W.index P).L), ((T (ι I)).index P).L := λ I,
      ⟨_, gg I, hgg I⟩,

      -- and we want to use the ts to define a compatible system over W.
    let z : (J.diagram P X).obj (op W) :=
      concrete.multiequalizer.mk _ _ (limit.is_limit _) (λ I, ts (ι I) (δ I)) _,
    swap,
    { sorry },

    -- This is the element we want to use...
    use (colimit.ι (J.diagram P X) (op W) z),

    -- Now we can use the conceret multiequalizer condition to show they're equal.

    apply concrete.multiequalizer.eq_of_forall_eq _ _ (limit.is_limit _),
    swap, apply_instance,

    intros I,
    change _ = s _,
    rw ← ht,

    -- apply separatedness condition
    apply plus_ext J P I.Y (T _),

    intros II,
    dsimp,
    simp only [← comp_apply],
    simp only [colimit.ι_pre, multiequalizer.lift_ι, ι_colim_map_assoc,
      category.assoc],
    dsimp only [plus_obj],
    simp only [colimit.ι_pre, multiequalizer.lift_ι, ι_colim_map_assoc,
      category.assoc, colimit.ι_pre_assoc],
    simp only [comp_apply],

    let ε : T I ⟶ (J.pullback I.f).obj W := hom_of_le begin
      intros Y f hf,
      apply sieve.le_pullback_bind _ _ _ I.hf,
      cases I,
      exact hf,
    end,

    erw ← colimit.w _ ((J.pullback II.f).op.map ε.op),
    simp only [comp_apply],

    congr' 1,

    dsimp,
    simp,

    apply concrete.multiequalizer.eq_of_forall_eq _ _ (limit.is_limit _),
    swap, apply_instance,

    intros III,
    simp only [← comp_apply],
    erw [multiequalizer.lift_ι, category.assoc, multiequalizer.lift_ι,
      category.assoc, multiequalizer.lift_ι, multiequalizer.lift_ι],

    dsimp [z],
    erw concrete.multiequalizer.mk_ι,
    change _ = ts I ⟨III.Y, III.f ≫ II.f, _⟩,
    dsimp [ι, δ, cover.map_L],
    --dsimp [ts],

    --cases I, cases II, cases III,
    --dsimp [ι, δ, cover.index, grothendieck_topology.cover.map_L,
    --  grothendieck_topology.cover.map_R],

    apply h _ ((J.pullback III.f).obj ((J.pullback II.f).obj ((J.pullback I.f).obj W))),

    intros IV,
    simp_rw ← comp_apply,
    rcases IV with ⟨IVY,IVf,IVhf⟩,
    dsimp,
    dsimp [pullback, sieve.pullback] at IVhf,
    obtain ⟨Z,h1,h2,h3,h4,h5⟩ := IVhf,
    dsimp at h4,
    sorry,
    --dsimp [pullback] at hℓ,
    /-
    let W : J.cover X := ⟨sieve.bind S (λ Y f hf, T ⟨Y,f,hf⟩),
      J.bind_covering S.condition (λ Y f hf, (T _).condition)⟩,
    let ZZ : Π ⦃Y⦄ (f : Y ⟶ X) (hf : W f), C := λ Y f hf, hf.some,
    let gg : Π ⦃Y⦄ (f : Y ⟶ X) (hf : W f), Y ⟶ (ZZ f hf) := λ Y f hf, hf.some_spec.some,
    let ee : Π ⦃Y⦄ (f : Y ⟶ X) (hf : W f), (ZZ f hf) ⟶ X := λ Y f hf, hf.some_spec.some_spec.some,
    have hee : ∀ ⦃Y⦄ (f : Y ⟶ X) (hf : W f), S (ee f hf) := λ Y f hf,
      hf.some_spec.some_spec.some_spec.some,
    have hee1 : ∀ ⦃Y⦄ (f : Y ⟶ X) (hf : W f), gg f hf ≫ ee f hf = f :=
      λ Y f hf, hf.some_spec.some_spec.some_spec.some_spec.2,
    have hee2 : ∀ ⦃Y⦄ (f : Y ⟶ X) (hf : W f),
      (T ⟨_, ee f hf, hee f hf⟩) (gg f hf) := λ Y f hf,
        hf.some_spec.some_spec.some_spec.some_spec.1,
    let z : (J.diagram P X).obj (op W) := concrete.multiequalizer.mk _ _ (limit.is_limit _)
      _ _,
    rotate,
    { intros I,
      exact multiequalizer.ι ((T ⟨_, ee I.f I.hf, hee I.f I.hf⟩).index P)
        ⟨_, gg I.f I.hf, hee2 I.f I.hf⟩ (y _) },
    { intros I,
      sorry,
    }
    -/
  }
end
-/

end category_theory.grothendieck_topology
