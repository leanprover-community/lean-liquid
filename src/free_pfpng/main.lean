import free_pfpng.basic
import condensed.projective_resolution
import condensed.condensify
import condensed.adjunctions
.

noncomputable theory

open category_theory

-- jmc: This is maybe not the best way to set things up.
-- The counit in `free_pfpng_profinite_natural_map` will probably be annoying

def profinite_to_condensed_unit :
  Profinite_to_Condensed ⟶
  condensify (free_pfpng_functor ⋙ ProFiltPseuNormGrp₁.to_CHFPNG₁) ⋙
    Condensed_Ab_to_CondensedSet :=
{ app := λ S, sorry, -- use a bit of Yoneda, maybe?
  naturality' := sorry }

def free_pfpng_profinite_natural_map :
  Profinite_to_Condensed ⋙ CondensedSet_to_Condensed_Ab ⟶
  condensify (free_pfpng_functor ⋙ ProFiltPseuNormGrp₁.to_CHFPNG₁) :=
(((whiskering_right _ _ _).obj CondensedSet_to_Condensed_Ab).map profinite_to_condensed_unit) ≫
  whisker_left
    (condensify (free_pfpng_functor ⋙ ProFiltPseuNormGrp₁.to_CHFPNG₁))
    Condensed_Ab_CondensedSet_adjunction.counit

instance : is_iso free_pfpng_profinite_natural_map := sorry

/-- Prop 2.1 of Analytic.pdf -/
def free_pfpng_profinite_iso :
  condensify (free_pfpng_functor ⋙ ProFiltPseuNormGrp₁.to_CHFPNG₁) ≅
  Profinite_to_Condensed ⋙ CondensedSet_to_Condensed_Ab :=
(as_iso free_pfpng_profinite_natural_map).symm

.

-- #check Condensed_Ab_CondensedSet_adjunction
