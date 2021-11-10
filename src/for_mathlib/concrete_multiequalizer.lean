import category_theory.limits.concrete_category
import category_theory.limits.shapes.multiequalizer

/-!
# Facts about (co)limits of functors into concrete categories
-/

universes w v u

open category_theory

namespace category_theory.limits

local attribute [instance] concrete_category.has_coe_to_fun concrete_category.has_coe_to_sort

variables {C : Type u} [category.{v} C] [concrete_category.{v} C]

lemma concrete.multiequalizer.eq_of_forall_eq (I : multicospan_index C)
  [preserves_limit I.multicospan (forget C)] (D : multifork I) (hD : is_limit D)
  (x y : D.X) (h : ∀ j : I.L, D.ι j x = D.ι j y) : x = y :=
begin
  apply concrete.is_limit_ext _ hD,
  rintros (a|b),
  { apply h },
  { rw ← D.w (walking_multicospan.hom.fst b),
    simp only [comp_apply],
    erw h,
    refl }
end

--lemma concrete.multiequalizer.condition (I : multicospan_index C)
--  [preserves_limit I.multicospan (forget C)] (D : multifork I) (hD : is_limit D)
--  (x : D.X) :

def concrete.multiequalizer.mk (I : multicospan_index C)
  [preserves_limit I.multicospan (forget C)] (D : multifork I) (hD : is_limit D)
  (xs : Π (t : I.L), I.left t) (rs : ∀ (s : I.R), I.fst s (xs _) = I.snd s (xs _)) :
  D.X :=
let E := (forget C).map_cone D,
  hE : is_limit E := is_limit_of_preserves _ hD,
  G : cone (I.multicospan ⋙ forget C) := types.limit_cone _,
  hG : is_limit G := types.limit_cone_is_limit _,
  e : G ≅ E := hG.unique_up_to_iso hE,
  eX : G.X ≅ E.X := (cones.forget _).map_iso e in
eX.hom ⟨λ t,
  match t with
  | walking_multicospan.left a := xs _
  | walking_multicospan.right b := I.fst b (xs _)
  end, begin
    rintros (a|b) (a|b) (_|_|_),
    { dsimp,
      change I.multicospan.map (𝟙 _) _ = _,
      rw I.multicospan.map_id,
      simp },
    { refl },
    { dsimp,
      erw ← rs,
      refl },
    { dsimp,
      change I.multicospan.map (𝟙 _) _ = _,
      rw I.multicospan.map_id,
      simp }
  end⟩

-- lemma concrete.multiequalizer.mk_ι (I : multicospan_index C)
--   [preserves_limit I.multicospan (forget C)] (D : multifork I) (hD : is_limit D)
--   (xs : Π (t : I.L), I.left t) (rs : ∀ (s : I.R), I.fst s (xs _) = I.snd s (xs _))
--   (t : I.L) :
--   D.ι t (concrete.multiequalizer.mk _ _ hD xs rs) = xs t := sorry

-- noncomputable def concrete.multiequalizer.equiv (I : multicospan_index C)
--   [preserves_limit I.multicospan (forget C)] [has_multiequalizer I] :
--   (multiequalizer I : C) ≃
--     { x : Π (a : I.L), I.left a // ∀ (b : I.R), (I.fst b) (x _) = (I.snd b) (x _) } :=
-- let E : (forget _).obj (multiequalizer I) ≅
--   (types.limit_cone (I.multicospan ⋙ forget C)).X :=
--     (is_limit_of_preserves (forget C) (limit.is_limit _)).cone_point_unique_up_to_iso
--       (types.limit_cone_is_limit _) in
-- equiv.trans E.to_equiv
-- { to_fun := λ x, ⟨λ i, x.1 (walking_multicospan.left _), sorry⟩,
--   inv_fun := λ x, ⟨λ i,
--   match i with
--   | walking_multicospan.left a := x.1 _
--   | walking_multicospan.right b := I.fst b (x.1 _)
--   end, sorry⟩,
--   left_inv := sorry,
--   right_inv := sorry }

end category_theory.limits
