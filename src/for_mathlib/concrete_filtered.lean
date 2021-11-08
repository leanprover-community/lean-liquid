import category_theory.limits.concrete_category

/-!
# Facts about (co)limits of functors into concrete categories
-/

universes w v u

open category_theory

namespace category_theory.limits

local attribute [instance] concrete_category.has_coe_to_fun concrete_category.has_coe_to_sort

variables {C : Type u} [category.{v} C] [concrete_category.{v} C]
  {J : Type v} [small_category J] (F : J ⥤ C) [preserves_colimit F (forget C)]

lemma concrete.colimit_eq_of_exists {a b : J} (x : F.obj a) (y : F.obj b)
  (h : ∃ (c : J) (f : a ⟶ c) (g : b ⟶ c), F.map f x = F.map g y)
  (E : cocone F) (hE : is_colimit E) : E.ι.app a x = E.ι.app b y :=
begin
  let G := (forget C).map_cocone E,
  let hG : is_colimit G := is_colimit_of_preserves _ hE,
  let D := types.colimit_cocone (F ⋙ forget C),
  let hD : is_colimit D := types.colimit_cocone_is_colimit _,
  let T : G ≅ D := hG.unique_up_to_iso hD,
  let TX : G.X ≅ D.X := (cocones.forget _).map_iso T,
  apply_fun TX.hom,
  swap, {
    have : function.bijective TX.hom, { rw ← is_iso_iff_bijective, exact is_iso.of_iso TX},
    exact this.1 },
  change (((forget C).map_cocone E).ι.app a ≫ TX.hom) x =
    (((forget C).map_cocone E).ι.app b ≫ TX.hom) y,
  erw [T.hom.w, T.hom.w],
  obtain ⟨c,f,g,h⟩ := h,
  let zx : D.X := (D.ι.app c) (F.map f x),
  have : ((D.ι.app a) x : D.X) = zx,
  { apply quot.sound,
    use f,
    refl },
  rw this,
  dsimp [zx],
  rw h,
  symmetry,
  apply quot.sound,
  use g,
  refl,
end

lemma concrete.colimit_exists_of_eq_of_filtered {a b : J} (x : F.obj a) (y : F.obj b)
  (E : cocone F) (hE : is_colimit E) (h : E.ι.app a x = E.ι.app b y)
  [is_filtered J] : ∃ (c : J) (f : a ⟶ c) (g : b ⟶ c), F.map f x = F.map g y :=
begin
  let G := (forget C).map_cocone E,
  let hG : is_colimit G := is_colimit_of_preserves _ hE,
  let D := types.colimit_cocone (F ⋙ forget C),
  let hD : is_colimit D := types.colimit_cocone_is_colimit _,
  let T : G ≅ D := hG.unique_up_to_iso hD,
  let TX : G.X ≅ D.X := (cocones.forget _).map_iso T,
  apply_fun TX.hom at h,
  change (((forget C).map_cocone E).ι.app a ≫ TX.hom) x =
  (((forget C).map_cocone E).ι.app b ≫ TX.hom) y at h,
  erw [T.hom.w, T.hom.w] at h,
  replace h := quot.exact _ h,
  have : ∀ (aa bb : Σ j, F.obj j) (h : eqv_gen (limits.types.quot.rel (F ⋙ forget C)) aa bb),
    ∃ (c : J) (f : aa.fst ⟶ c) (g : bb.fst ⟶ c), F.map f aa.snd =  F.map g bb.snd,
  { intros aa bb hh,
    induction hh,
    case eqv_gen.rel : aa bb hh {
      obtain ⟨f,hf⟩ := hh,
      use [bb.fst, f, 𝟙 _],
      simpa using hf.symm },
    case eqv_gen.refl : aaa { use [aaa.fst, 𝟙 _, 𝟙 _] },
    case eqv_gen.symm : aa bb hh1 hh2 {
      obtain ⟨c,f,g,h⟩ := hh2,
      use [c, g, f],
      exact h.symm },
    case eqv_gen.trans : aa bb cc hh1 hh2 hh3 hh4 {
      obtain ⟨c1,f1,g1,h1⟩ := hh3,
      obtain ⟨c2,f2,g2,h2⟩ := hh4,
      let c0 := is_filtered.max c1 c2,
      let e1 : c1 ⟶ c0 := is_filtered.left_to_max _ _,
      let e2 : c2 ⟶ c0 := is_filtered.right_to_max _ _,
      let c := is_filtered.coeq (g1 ≫ e1) (f2 ≫ e2),
      let e : c0 ⟶ c := is_filtered.coeq_hom _ _,
      use [c, f1 ≫ e1 ≫ e, g2 ≫ e2 ≫ e],
      simp only [F.map_comp, comp_apply, h1, ← h2],
      simp_rw [← comp_apply, ← F.map_comp],
      rw is_filtered.coeq_condition } },
  exact this ⟨a,x⟩ ⟨b,y⟩ h,
end

end category_theory.limits
