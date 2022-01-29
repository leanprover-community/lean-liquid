import pseudo_normed_group.category
import for_mathlib.ab_explicit_limits

open category_theory
open category_theory.limits

universe u
variables {J : Type u} [small_category J]

-- We can develop all this stuff for `CompHausFiltPseuNormGrp₁` as well, if needed.
namespace ProFiltPseuNormGrp₁

def to_Ab : ProFiltPseuNormGrp₁.{u} ⥤ Ab.{u} :=
{ obj := λ M, AddCommGroup.of M,
  map := λ M N f, f.to_add_monoid_hom }

variable {K : J ⥤ ProFiltPseuNormGrp₁.{u}}
variable (C : limits.limit_cone (K ⋙ to_Ab))

def bounded_elements : add_subgroup C.cone.X :=
{ carrier := { x | ∃ c, ∀ j, C.cone.π.app j x ∈ pseudo_normed_group.filtration (K.obj j) c },
  zero_mem' := ⟨0, λ j, by { simp, apply pseudo_normed_group.zero_mem_filtration } ⟩,
  add_mem' := λ a b ha hb, begin
    obtain ⟨c,hc⟩ := ha,
    obtain ⟨d,hd⟩ := hb,
    use c + d,
    intros j,
    simp,
    apply pseudo_normed_group.add_mem_filtration,
    apply hc,
    apply hd,
  end,
  neg_mem' := λ a ha, begin
    obtain ⟨c,hc⟩ := ha,
    use c,
    intros j,
    simp,
    apply pseudo_normed_group.neg_mem_filtration,
    apply hc,
  end }

def bounded_elements.filt (c : nnreal) : set C.cone.X :=
{ x | ∀ j, C.cone.π.app j x ∈ pseudo_normed_group.filtration (K.obj j) c }

def bounded_elements.filt_incl (c : nnreal) :
  bounded_elements.filt C c → bounded_elements C :=
λ x, ⟨x, c, x.2⟩

def bounded_elements.filtration (c : nnreal) : set (bounded_elements C) :=
set.range (bounded_elements.filt_incl _ c)

def bounded_elements.filtration_equiv (c : nnreal) :
  bounded_elements.filtration C c ≃ (Profinite.limit_cone (K ⋙ level.obj c)).X :=
{ to_fun := λ t, ⟨λ j, ⟨C.cone.π.app _ t.1.1, sorry⟩, sorry⟩,
  inv_fun := λ t,
    let e := (Ab.explicit_limit_cone_is_limit (K ⋙ to_Ab)).cone_point_unique_up_to_iso
      (C.2 : is_limit C.1) in
  { val := ⟨e.hom ⟨λ j, (t.1 j).1, sorry⟩, sorry⟩,
    property := sorry },
  left_inv := sorry,
  right_inv := sorry }

instance (c : nnreal) :
  topological_space (bounded_elements.filtration C c) :=
topological_space.induced (bounded_elements.filtration_equiv C c) infer_instance

instance (c : nnreal) :
  t2_space (bounded_elements.filtration C c) := sorry

instance (c : nnreal) :
  compact_space (bounded_elements.filtration C c) := sorry

instance (c : nnreal) :
  totally_disconnected_space (bounded_elements.filtration C c) := sorry

def bounded_cone_point : ProFiltPseuNormGrp₁ :=
{ M := bounded_elements C,
  str :=
  { filtration := bounded_elements.filtration _,
  filtration_mono := sorry,
  zero_mem_filtration := sorry,
  neg_mem_filtration := sorry,
  add_mem_filtration := sorry,
  continuous_add' := sorry,
  continuous_neg' := sorry,
  continuous_cast_le := sorry },
  exhaustive' := begin
    intros m,
    obtain ⟨c,hc⟩ := m.2,
    refine ⟨c,⟨m.1, hc⟩, by { ext, refl }⟩,
  end }

def bounded_cone : cone K :=
{ X := bounded_cone_point C,
  π :=
  { app := λ j,
    { to_fun := λ x, C.cone.π.app _ x.1,
      map_zero' := sorry,
      map_add' := sorry,
      strict' := sorry,
      continuous' := sorry },
    naturality' := sorry } }

def bounded_cone_is_limit : is_limit (bounded_cone C) :=
{ lift := λ S,
  { to_fun := λ x, ⟨C.2.lift (to_Ab.map_cone S) x, sorry⟩,
    map_zero' := sorry,
    map_add' := sorry,
    strict' := sorry,
    continuous' := sorry },
  fac' := sorry,
  uniq' := sorry }

end ProFiltPseuNormGrp₁
