import condensed.top_comparison

open category_theory

namespace Condensed

universes u
variables {X Y : Condensed.{u} Ab.{u+1}} (f : X ⟶ Y)

lemma is_iso_iff_ExtrDisc :
  is_iso f ↔ (∀ S : ExtrDisc, is_iso (f.val.app (opposite.op S.val))) :=
begin
  split,
  { introsI h S,
    change is_iso ((Condensed.evaluation _ _).map f),
    apply_instance },
  { introsI h,
    suffices : is_iso ((Condensed_ExtrSheafProd_equiv Ab).functor.map f),
    { resetI,
      apply is_iso_of_fully_faithful (Condensed_ExtrSheafProd_equiv Ab.{u+1}).functor f },
    suffices : is_iso (((ExtrSheafProd_to_presheaf Ab.{u+1})).map
      ((Condensed_ExtrSheafProd_equiv Ab.{u+1}).functor.map f)),
    { resetI,
      apply is_iso_of_fully_faithful (ExtrSheafProd_to_presheaf Ab.{u+1}) },
    apply_with nat_iso.is_iso_of_is_iso_app { instances := ff },
    intros S, apply h }
end

end Condensed
