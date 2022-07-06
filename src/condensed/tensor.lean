import condensed.adjunctions
import condensed.extr.equivalence
import condensed.short_exact

import for_mathlib.AddCommGroup.tensor

noncomputable theory

universes u
open_locale tensor_product

open category_theory

namespace ExtrSheafProd

@[simps obj map]
def tensor_presheaf (M : ExtrDisc.{u}ᵒᵖ ⥤ Ab.{u+1}) (A : Ab.{u+1}) :
  ExtrDisc.{u}ᵒᵖ ⥤ Ab.{u+1} :=
M ⋙ AddCommGroup.tensor_functor.flip.obj A

@[simps val]
def tensor (M : ExtrSheafProd.{u} Ab.{u+1}) (A : Ab.{u+1}) :
  ExtrSheafProd.{u} Ab.{u+1} :=
{ val := tensor_presheaf M.val A,
  cond := begin
    introsI α _ X, dsimp [tensor_presheaf, AddCommGroup.tensor_functor],
    let e := _, change is_iso e,
    have hq := M.cond _ X, dsimp at hq, let q := _, change is_iso q at hq,
    have he : e = AddCommGroup.map_tensor q (𝟙 _) ≫
      AddCommGroup.tensor_pi_comparison _ _,
    { ext1 j,
      dsimp [AddCommGroup.tensor_pi_comparison],
      simp only [←AddCommGroup.map_tensor_comp_left, limits.limit.lift_π,
        limits.fan.mk_π_app, category.assoc]},
    rw he, resetI, apply_with is_iso.comp_is_iso { instances := ff },
    swap, apply_instance,
    use AddCommGroup.map_tensor (inv q) (𝟙 _),
    split,
    { rw [← AddCommGroup.map_tensor_comp_left, is_iso.hom_inv_id, AddCommGroup.map_tensor_id], },
    { rw [← AddCommGroup.map_tensor_comp_left, is_iso.inv_hom_id, AddCommGroup.map_tensor_id], },
  end } -- tensor products commutes with direct sums.

@[simps val_app]
def map_tensor {M M' : ExtrSheafProd.{u} Ab.{u+1}} {A A' : AddCommGroup.{u+1}}
  (f : M ⟶ M') (g : A ⟶ A') :
  M.tensor A ⟶ M'.tensor A' := ExtrSheafProd.hom.mk $
{ app := λ S, AddCommGroup.map_tensor (f.val.app _) g,
  naturality' := begin
    intros X Y i,
    dsimp [tensor, tensor_presheaf],
    simp only [← AddCommGroup.map_tensor_comp_comp, category.id_comp, category.comp_id,
      f.val.naturality],
  end }

@[simp]
lemma map_tensor_id (M : ExtrSheafProd.{u} Ab.{u+1}) (A : AddCommGroup.{u+1}) :
  map_tensor (𝟙 M) (𝟙 A) = 𝟙 _ :=
by { ext : 3, dsimp, simp }

@[simp]
lemma map_tensor_comp {M M' M'' : ExtrSheafProd.{u} Ab.{u+1}}
  {A A' A'' : AddCommGroup.{u+1}}
  (f : M ⟶ M') (f' : M' ⟶ M'')
  (g : A ⟶ A') (g' : A' ⟶ A'') :
  map_tensor (f ≫ f') (g ≫ g') = map_tensor f g ≫ map_tensor f' g' :=
by { ext : 3, dsimp, simp }

-- Slow, so probably break into pieces
@[simps]
def tensor_functor : ExtrSheafProd.{u} Ab.{u+1} ⥤ Ab.{u+1} ⥤ ExtrSheafProd.{u} Ab.{u+1} :=
{ obj := λ M,
  { obj := λ A, M.tensor A,
    map := λ A A' f, map_tensor (𝟙 _) f,
    map_id' := λ X, by simp,
    map_comp' := λ X Y Z f g, begin
      nth_rewrite 0 [← category.id_comp (𝟙 M)],
      rw map_tensor_comp,
    end },
  map := λ M N f,
  { app := λ A, map_tensor f (𝟙 _),
    naturality' := λ A B g, begin
      dsimp,
      simp only [← map_tensor_comp, category.id_comp, category.comp_id],
    end },
  map_id' := λ M, begin
    ext : 2,
    simp,
  end,
  map_comp' := λ M N L f g, begin
    ext x : 2,
    dsimp,
    nth_rewrite 0 [← category.comp_id (𝟙 x)],
    rw [map_tensor_comp],
  end }
.

@[simps]
instance hom_has_add {M N : ExtrSheafProd.{u} Ab.{u+1}} : has_add (M ⟶ N) :=
⟨λ f g, ⟨f.val + g.val⟩⟩

@[simps]
instance hom_has_zero {M N : ExtrSheafProd.{u} Ab.{u+1}} : has_zero (M ⟶ N) :=
⟨⟨0⟩⟩

@[simps]
instance hom_has_neg {M N : ExtrSheafProd.{u} Ab.{u+1}} : has_neg (M ⟶ N) :=
⟨λ f, ⟨-f.val⟩⟩

@[simps]
instance hom_has_sub {M N : ExtrSheafProd.{u} Ab.{u+1}} : has_sub (M ⟶ N) :=
⟨λ f g, ⟨f.val - g.val⟩⟩

instance preadditive : preadditive (ExtrSheafProd.{u} Ab.{u+1}) :=
{ hom_group := λ P Q,
  { add_assoc := λ f g h, by { ext1, dsimp, rw add_assoc },
    zero_add := λ f, by { ext1, dsimp, rw zero_add },
    add_zero := λ f, by { ext1, dsimp, rw add_zero },
    nsmul := λ n f, ⟨n • f.val⟩,
    nsmul_zero' := λ f, by { ext1, dsimp, simp, },
    nsmul_succ' := λ n f, by { ext1, dsimp, exact succ_nsmul f.val n },
    sub_eq_add_neg := λ f g, by { ext1, dsimp, exact sub_eq_add_neg f.val g.val },
    zsmul := λ n f, ⟨n • f.val⟩,
    zsmul_zero' := λ f, by { ext1, dsimp, simp },
    zsmul_succ' := λ n f, by { ext1, dsimp, rw [add_zsmul, one_zsmul, add_comm], },
    zsmul_neg' := λ n f, by { ext1, dsimp, simpa, },
    add_left_neg := λ f, by { ext1, dsimp, simp },
    add_comm := λ f g, by { ext1, dsimp, rw add_comm },
    ..(infer_instance : has_add _),
    ..(infer_instance : has_neg _),
    ..(infer_instance : has_zero _),
    ..(infer_instance : has_sub _) },
  add_comp' := λ P Q R f f' g, by { ext1, dsimp, simp },
  comp_add' := λ P Q R f g g', by { ext1, dsimp, simp } }

def evaluation (S : ExtrDisc.{u}) :
  ExtrSheafProd.{u} Ab.{u+1} ⥤ Ab.{u+1} :=
ExtrSheafProd_to_presheaf _ ⋙ (evaluation _ _).obj (opposite.op S)

instance evaluation_additive (S) : functor.additive (evaluation S) :=
⟨λ M N f g, rfl⟩

@[simps]
def half_internal_hom (A : AddCommGroup.{u+1}) (M : ExtrSheafProd.{u} Ab.{u+1}) :
  ExtrSheafProd.{u} Ab.{u+1} :=
{ val :=
  { obj := λ S, AddCommGroup.of (A ⟶ M.val.obj S),
    map := λ X Y f, (preadditive_yoneda.flip.obj (opposite.op A)).map $ M.val.map f,
    map_id' := begin
      intros S,
      dsimp, simpa,
    end,
    map_comp' := begin
      intros R S T f g,
      dsimp,
      simp,
    end },
  cond := begin
    introsI α _ X, dsimp,
    let t := _, change is_iso t,
    have := M.cond α X, dsimp at this, let e := _, change is_iso e at this, resetI,
    let q : AddCommGroup.of (A ⟶ M.val.obj (opposite.op (ExtrDisc.sigma X))) ≅
      AddCommGroup.of (A ⟶ (∏ (λ i, M.val.obj (opposite.op (X i))))) :=
      (preadditive_yoneda.flip.obj (opposite.op A)).map_iso (as_iso e),
    let s : AddCommGroup.of (A ⟶ (∏ (λ i, M.val.obj (opposite.op (X i))))) ⟶
      ∏ (λ i, AddCommGroup.of (A ⟶ M.val.obj (opposite.op (X i)))) :=
      limits.pi.lift (λ i, (preadditive_yoneda.flip.obj (opposite.op A)).map
        (limits.pi.π _ i)),
    have ht : t = q.hom ≫ s,
    { dsimp [t, q, s, e], ext1,
      simp only [limits.limit.lift_π, limits.fan.mk_π_app, category.assoc],
      rw [← nat_trans.comp_app, ← functor.map_comp, limits.limit.lift_π],
      refl },
    rw ht, clear ht,
    suffices : is_iso s,
    { resetI, apply is_iso.comp_is_iso },
    -- Now we need to show that `Hom(A,(Π i, X i)) = Π i, Hom(A,X i)`.
    apply AddCommGroup.is_iso_hom_product_comparison.{u u+1},
  end }

def tensor_uncurry {A : AddCommGroup.{u+1}} {M N : ExtrSheafProd.{u} Ab.{u+1}}
  (e : M ⟶ half_internal_hom A N) :
  tensor M A ⟶ N := ExtrSheafProd.hom.mk $
{ app := λ S, AddCommGroup.tensor_uncurry $ e.val.app _,
  naturality' := begin
    intros X Y f,
    erw ← AddCommGroup.tensor_uncurry_comp_curry,
    apply (AddCommGroup.tensor_curry_equiv _ _ _).injective,
    erw (AddCommGroup.tensor_curry_equiv _ _ _).apply_symm_apply,
    dsimp [AddCommGroup.tensor_curry_equiv],
    erw [AddCommGroup.tensor_curry_uncurry_comp, ← nat_trans.naturality,
      ← AddCommGroup.tensor_curry_equiv_apply,
      ← AddCommGroup.tensor_curry_equiv_symm_apply,
      (AddCommGroup.tensor_curry_equiv _ _ _).apply_symm_apply],
  end }

def tensor_curry {A : AddCommGroup.{u+1}} {M N : ExtrSheafProd.{u} Ab.{u+1}}
  (e : M.tensor A ⟶ N) : M ⟶ half_internal_hom A N := ExtrSheafProd.hom.mk $
{ app := λ S, AddCommGroup.tensor_curry $ e.val.app _,
  naturality' := begin
    intros X Y f,
    dsimp [half_internal_hom],
    erw [← AddCommGroup.tensor_curry_uncurry_comp],
    apply (AddCommGroup.tensor_curry_equiv _ _ _).symm.injective,
    simp_rw ← AddCommGroup.tensor_curry_equiv_apply,
    rw (AddCommGroup.tensor_curry_equiv _ _ _).symm_apply_apply,
    rw ← AddCommGroup.tensor_curry_equiv_symm_apply,
    rw (AddCommGroup.tensor_curry_equiv _ _ _).symm_apply_apply,
    dsimp,
    rw [AddCommGroup.tensor_uncurry_comp_curry, ← nat_trans.naturality],
    refl,
  end }

lemma tensor_curry_uncurry {A : AddCommGroup.{u+1}} {M N : ExtrSheafProd.{u} Ab.{u+1}}
  (e : M ⟶ half_internal_hom A N) :
  tensor_curry (tensor_uncurry e) = e :=
begin
  ext S : 3,
  dsimp [tensor_curry, tensor_uncurry],
  simp,
end

lemma tensor_uncurry_curry {A : AddCommGroup.{u+1}} {M N : ExtrSheafProd.{u} Ab.{u+1}}
  (e : M.tensor A ⟶ N) :
  tensor_uncurry (tensor_curry e) = e :=
begin
  ext S : 3,
  dsimp [tensor_curry, tensor_uncurry],
  simp,
end

end ExtrSheafProd

namespace ExtrSheaf

def tensor (M : ExtrSheaf.{u} Ab.{u+1}) (A : AddCommGroup.{u+1}) :
  ExtrSheaf.{u} Ab.{u+1} :=
(ExtrSheaf_ExtrSheafProd_equiv _).inverse.obj $
((ExtrSheaf_ExtrSheafProd_equiv _).functor.obj M).tensor A

@[simp]
lemma tensor_val_obj (M : ExtrSheaf.{u} Ab.{u+1}) (A : AddCommGroup.{u+1}) (T) :
  (M.tensor A).val.obj T = (M.val.obj T).tensor A := rfl

def half_internal_hom (A : AddCommGroup.{u+1}) (M : ExtrSheaf.{u} Ab.{u+1}) :
  ExtrSheaf.{u} Ab.{u+1} :=
(ExtrSheaf_ExtrSheafProd_equiv _).inverse.obj $
((ExtrSheaf_ExtrSheafProd_equiv _).functor.obj M).half_internal_hom A

@[simp]
lemma half_internal_hom_val_obj (A : AddCommGroup.{u+1}) (M : ExtrSheaf.{u} Ab.{u+1}) (T) :
  (M.half_internal_hom A).val.obj T =
  AddCommGroup.of (A ⟶ M.val.obj T) := rfl

def tensor_curry {A : AddCommGroup.{u+1}} {M N : ExtrSheaf.{u} Ab.{u+1}}
  (e : M.tensor A ⟶ N) :
  M ⟶ N.half_internal_hom A :=
⟨(ExtrSheafProd.tensor_curry $ (ExtrSheaf_ExtrSheafProd_equiv _).functor.map e).val⟩

def tensor_uncurry {A : AddCommGroup.{u+1}} {M N : ExtrSheaf.{u} Ab.{u+1}}
  (e : M ⟶ N.half_internal_hom A) :
  M.tensor A ⟶ N :=
⟨(ExtrSheafProd.tensor_uncurry $ (ExtrSheaf_ExtrSheafProd_equiv _).functor.map e).val⟩

@[simps val]
def map_tensor {M M' : ExtrSheaf.{u} Ab.{u+1}} {A A' : AddCommGroup.{u+1}}
  (f : M ⟶ M') (g : A ⟶ A') :
  M.tensor A ⟶ M'.tensor A' :=
⟨((ExtrSheafProd.map_tensor $ (ExtrSheaf_ExtrSheafProd_equiv _).functor.map f) g).val⟩

@[simp]
lemma map_tensor_id (M : ExtrSheaf.{u} Ab.{u+1}) (A : AddCommGroup.{u+1}) :
  map_tensor (𝟙 M) (𝟙 A) = 𝟙 _ :=
by { ext : 1, dsimp, simpa, }

@[simp]
lemma map_tensor_comp {M M' M'' : ExtrSheaf.{u} Ab.{u+1}}
  {A A' A'' : AddCommGroup.{u+1}}
  (f : M ⟶ M') (f' : M' ⟶ M'')
  (g : A ⟶ A') (g' : A' ⟶ A'') :
  map_tensor (f ≫ f') (g ≫ g') = map_tensor f g ≫ map_tensor f' g' :=
by { ext : 1, dsimp, simp }

@[simps]
def tensor_functor : ExtrSheaf.{u} Ab.{u+1} ⥤ Ab.{u+1} ⥤ ExtrSheaf.{u} Ab.{u+1} :=
{ obj := λ M,
  { obj := λ A, M.tensor A,
    map := λ A A' f, map_tensor (𝟙 _) f,
    map_id' := λ X, by simp,
    map_comp' := λ X Y Z f g, begin
      nth_rewrite 0 [← category.id_comp (𝟙 M)],
      rw map_tensor_comp,
    end },
  map := λ M N f,
  { app := λ A, map_tensor f (𝟙 _),
    naturality' := λ A B g, begin
      dsimp,
      simp only [← map_tensor_comp, category.id_comp, category.comp_id],
    end },
  map_id' := λ M, begin
    ext : 2,
    simp,
  end,
  map_comp' := λ M N L f g, begin
    ext x : 2,
    dsimp,
    nth_rewrite 0 [← category.comp_id (𝟙 x)],
    rw [map_tensor_comp],
  end }

instance creates_colimits :
  creates_colimits
  (Sheaf_to_presheaf ExtrDisc.proetale_topology.{u} Ab.{u+1}) :=
show creates_colimits ((ExtrSheaf_ExtrSheafProd_equiv _).functor ⋙
  ExtrSheafProd_to_presheaf _), from infer_instance

instance preserves_colimits_tensor_obj (M : ExtrSheaf.{u} Ab.{u+1}) :
  limits.preserves_colimits (tensor_functor.obj M) :=
begin
  constructor, introsI J _, constructor, intros F, constructor, intros S hS,
  let T := _, change (limits.is_colimit T),
  apply limits.is_colimit_of_reflects
    (Sheaf_to_presheaf ExtrDisc.proetale_topology.{u} Ab.{u+1}),
  apply limits.evaluation_jointly_reflects_colimits,
  intros Q,
  change limits.is_colimit
    ((AddCommGroup.tensor_functor.obj (M.val.obj Q)).map_cocone S),
  apply limits.is_colimit_of_preserves,
  exact hS,
end

example (α : Type (u+1)) (N : ExtrSheaf.{u} Ab.{u+1}) :
limits.preserves_colimits_of_shape (discrete α) (tensor_functor.obj N) := infer_instance

end ExtrSheaf

namespace Condensed

def tensor (M : Condensed.{u} Ab.{u+1}) (A : Ab.{u+1}) :
  Condensed.{u} Ab.{u+1} :=
(Condensed_ExtrSheaf_equiv _).functor.obj
(((Condensed_ExtrSheaf_equiv _).inverse.obj M).tensor A)

def map_tensor {M M' : Condensed.{u} Ab.{u+1}} {A A' : Ab.{u+1}}
  (f : M ⟶ M') (g : A ⟶ A') :
  M.tensor A ⟶ M'.tensor A' :=
(Condensed_ExtrSheaf_equiv _).functor.map $
ExtrSheaf.map_tensor ((Condensed_ExtrSheaf_equiv _).inverse.map f) g

@[simp]
lemma map_tensor_id (M : Condensed.{u} Ab.{u+1}) (A : AddCommGroup.{u+1}) :
  map_tensor (𝟙 M) (𝟙 A) = 𝟙 _ :=
by { dsimp [map_tensor], simpa, }

@[simp]
lemma map_tensor_comp {M M' M'' : Condensed.{u} Ab.{u+1}}
  {A A' A'' : AddCommGroup.{u+1}}
  (f : M ⟶ M') (f' : M' ⟶ M'')
  (g : A ⟶ A') (g' : A' ⟶ A'') :
  map_tensor (f ≫ f') (g ≫ g') = map_tensor f g ≫ map_tensor f' g' :=
by { dsimp [map_tensor], simp, }

/-- This is the functor that sends `A : Ab` to `M ⊗ A`,
where `M` is a condensed abelian group, functorial in both `M` and `A`. -/
def tensor_functor : Condensed.{u} Ab.{u+1} ⥤ Ab.{u+1} ⥤ Condensed.{u} Ab.{u+1} :=
{ obj := λ M,
  { obj := λ A, M.tensor A,
    map := λ A A' f, map_tensor (𝟙 _) f,
    map_id' := λ X, by simp,
    map_comp' := λ X Y Z f g, begin
      nth_rewrite 0 [← category.id_comp (𝟙 M)],
      rw map_tensor_comp,
    end },
  map := λ M N f,
  { app := λ A, map_tensor f (𝟙 _),
    naturality' := λ A B g, begin
      dsimp,
      simp only [← map_tensor_comp, category.id_comp, category.comp_id],
    end },
  map_id' := λ M, begin
    ext : 2,
    simp,
  end,
  map_comp' := λ M N L f g, begin
    ext x : 2,
    dsimp,
    nth_rewrite 0 [← category.comp_id (𝟙 x)],
    rw [map_tensor_comp],
  end }

/-
/-- Restrincting to `ExtrDisc` works as expeceted. -/
def tensor_functor_conj_iso :
  (Condensed_ExtrSheaf_equiv Ab.{u+1}).functor ⋙
  ((whiskering_right _ _ _).obj $ ((whiskering_right _ _ _).obj
    (Condensed_ExtrSheaf_equiv Ab.{u+1}).inverse)).obj tensor_functor ≅
  ExtrSheaf.tensor_functor :=
nat_iso.of_components
(λ X, begin
  dsimp [tensor_functor],
end)
begin
  intros X Y f, ext : 2,
  dsimp [tensor_functor],
  simp only [equivalence.fun_inv_map, equivalence.equivalence_mk'_counit,
    equivalence.equivalence_mk'_counit_inv, functor.map_comp, nat_trans.comp_app,
    category.assoc, iso.inv_hom_id_app_assoc, category.id_comp,
    nat_iso.cancel_nat_iso_hom_left],
  rw [← nat_trans.comp_app, ← functor.map_comp, ← nat_trans.comp_app],
  have : (Condensed_ExtrSheafProd_equiv Ab).counit_iso.inv.app Y ≫
    (Condensed_ExtrSheafProd_equiv Ab).counit_iso.hom.app Y = 𝟙 _,
  { rw [← nat_trans.comp_app, iso.inv_hom_id], refl },
  rw this,
  simp only [nat_trans.comp_app],
  dsimp,
  simp only [category_theory.functor.map_id, nat_trans.id_app, category.comp_id],
end

def tensor_functor_conj_iso' :
  tensor_functor ⋙ (whiskering_right _ _ _).obj
  (Condensed_ExtrSheafProd_equiv _).functor ≅
  (Condensed_ExtrSheafProd_equiv _).functor ⋙ ExtrSheafProd.tensor_functor :=
nat_iso.of_components
(λ X, begin
  dsimp [tensor_functor],
  refine functor.associator _ _ _ ≪≫ _,
  refine _ ≪≫ functor.right_unitor _,
  refine ((whiskering_left _ _ _).obj _).map_iso _,
  refine (Condensed_ExtrSheafProd_equiv _).counit_iso,
end)
begin
  intros X Y f, ext : 2,
  dsimp [tensor_functor],
  simp, dsimp, simp,
end
-/

def tensor_iso (M : Condensed.{u} Ab.{u+1}) (A : Ab.{u+1}) :
  (Condensed_ExtrSheaf_equiv _).inverse.obj (M.tensor A) ≅
  ((Condensed_ExtrSheaf_equiv _).inverse.obj M).tensor A :=
((Condensed_ExtrSheaf_equiv _).unit_iso.app _).symm

/-- The tensor product behaves in the naive way when evaluated
on extremally disconnected sets. -/
def tensor_eval_iso
  (M : Condensed.{u} Ab.{u+1}) (A : Ab.{u+1}) (S : ExtrDisc.{u}) :
  (tensor M A).val.obj (opposite.op S.val) ≅
  ((M.val.obj (opposite.op S.val)).tensor A) :=
((Sheaf_to_presheaf _ _).map_iso (M.tensor_iso A)).app (opposite.op S)

def half_internal_hom (A : AddCommGroup.{u+1}) (M : Condensed.{u} Ab.{u+1}) :
  Condensed.{u} Ab.{u+1} :=
(Condensed_ExtrSheaf_equiv _).functor.obj $
ExtrSheaf.half_internal_hom A ((Condensed_ExtrSheaf_equiv _).inverse.obj M)

def half_internal_hom_iso (A : AddCommGroup.{u+1}) (M : Condensed.{u} Ab.{u+1}) :
  (Condensed_ExtrSheaf_equiv _).inverse.obj (half_internal_hom A M) ≅
  ExtrSheaf.half_internal_hom A ((Condensed_ExtrSheaf_equiv _).inverse.obj M) :=
((Condensed_ExtrSheaf_equiv _).unit_iso.app _).symm

def half_internal_hom_eval_iso (A : AddCommGroup.{u+1}) (M : Condensed.{u} Ab.{u+1})
  (S : ExtrDisc.{u}) :
  (half_internal_hom A M).val.obj (opposite.op S.val) ≅
  AddCommGroup.of (A ⟶ M.val.obj (opposite.op S.val)) :=
((Sheaf_to_presheaf _ _).map_iso (half_internal_hom_iso A M)).app (opposite.op S)

def tensor_uncurry {A : AddCommGroup.{u+1}} {M N : Condensed.{u} Ab.{u+1}}
  (e : M ⟶ half_internal_hom A N) :
  tensor M A ⟶ N :=
(Condensed_ExtrSheaf_equiv _).functor.map
  (ExtrSheaf.tensor_uncurry $ (Condensed_ExtrSheaf_equiv Ab).inverse.map e ≫
  (half_internal_hom_iso _ _).hom) ≫
  ((Condensed_ExtrSheaf_equiv _).counit_iso.app N).hom

lemma tensor_uncurry_eq
  {A : AddCommGroup.{u+1}} {M N : Condensed.{u} Ab.{u+1}}
  (e : M ⟶ half_internal_hom A N) :
  (Condensed_ExtrSheaf_equiv _).inverse.map (tensor_uncurry e) =
  (tensor_iso _ _).hom ≫
  ExtrSheaf.tensor_uncurry
  ((Condensed_ExtrSheaf_equiv _).inverse.map e ≫ (half_internal_hom_iso _ _).hom) :=
begin
  dsimp [tensor_uncurry, half_internal_hom_iso, tensor_iso],
  simp,
end

def tensor_curry {A : AddCommGroup.{u+1}} {M N : Condensed.{u} Ab.{u+1}}
  (e : M.tensor A ⟶ N) : M ⟶ half_internal_hom A N :=
  ((Condensed_ExtrSheaf_equiv _).counit_iso.app _).inv ≫
  (Condensed_ExtrSheaf_equiv _).functor.map
  (ExtrSheaf.tensor_curry $ (tensor_iso M A).inv ≫
  (Condensed_ExtrSheaf_equiv Ab).inverse.map e)

lemma tensor_curry_eq {A : AddCommGroup.{u+1}} {M N : Condensed.{u} Ab.{u+1}}
  (e : M.tensor A ⟶ N) :
  (Condensed_ExtrSheaf_equiv _).inverse.map (tensor_curry e) =
  ExtrSheaf.tensor_curry ((tensor_iso _ _).inv ≫
    (Condensed_ExtrSheaf_equiv Ab).inverse.map e) ≫
  (half_internal_hom_iso _ _).inv :=
begin
  rw iso.eq_comp_inv,
  dsimp [tensor_curry, half_internal_hom_iso, tensor_iso],
  simp only [functor.map_comp, equivalence.fun_inv_map, equivalence.equivalence_mk'_counit,
    category.assoc, iso.inv_hom_id_app],
  simp, dsimp, simp,
  --dsimp,
  --simp only [category.comp_id],
  suffices :
    (Condensed_ExtrSheaf_equiv Ab).inverse.map
      ((Condensed_ExtrSheaf_equiv Ab).counit_iso.inv.app M) ≫
    (Condensed_ExtrSheaf_equiv Ab).unit_iso.inv.app
      ((Condensed_ExtrSheaf_equiv Ab).inverse.obj M) = 𝟙 _,
  { rw reassoc_of this },
  simpa,
end

def tensor_functor_iso_ExtrSheaf_tensor_functor (M : Condensed.{u} Ab.{u+1}) :
  tensor_functor.obj M ≅
    (ExtrSheaf.tensor_functor.obj
      ((Condensed_ExtrSheaf_equiv _).inverse.obj M)) ⋙
    (Condensed_ExtrSheaf_equiv _).functor := by refl

instance (M : Condensed.{u} Ab.{u+1}) :
  limits.preserves_colimits (tensor_functor.obj M) :=
limits.preserves_colimits_of_nat_iso (tensor_functor_iso_ExtrSheaf_tensor_functor M).symm

example (α : Type (u+1)) (M : Condensed.{u} Ab.{u+1}) :
  limits.preserves_colimits_of_shape (discrete α) (tensor_functor.obj M) :=
infer_instance

end Condensed
