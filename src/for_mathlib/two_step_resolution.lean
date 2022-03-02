import for_mathlib.pid
import for_mathlib.projectives
import algebra.category.Module.projective
import for_mathlib.AddCommGroup.exact


noncomputable theory

open Module category_theory category_theory.limits

open_locale zero_object


lemma nat.eq_zero_or_exists_eq_add_of_ne_one {i : ℕ} (h : i ≠ 1) :
i = 0 ∨ ∃ k : ℕ, i = k + 2 :=
begin
  by_cases hi : i = 0,
  exact or.intro_left _ hi,
  simp at h,
  have : 2 ≤ i := nat.one_lt_iff_ne_zero_and_ne_one.2 ⟨hi, h⟩,
  have := or.intro_right _ (nat.exists_eq_add_of_le this),
  simpa [add_comm]
end


universes u v

variables (R : Type u) [comm_ring R] (M : Type (max u v)) [add_comm_group M] [module R M]

@[instance]
lemma Module.projective_of_of_projective [h : module.projective.{u v} R M] : category_theory.projective (of R M) :=
is_projective.iff_projective.1 h


/-- The objects of the two step ""resolution" of a module over a commutative ring. -/
def two_step_resolution_X : ℕ → Module.{max v u} R
| 0 := Module.of R (M →₀ R)
| 1 := Module.of R ((finsupp.total M M R id).ker)
| (n+2) := 0


/--  The objects of the two step projective resolution of an Abelian group .-/
def two_step_resolution_ab_X (M : Type v) [add_comm_group M] : ℕ → AddCommGroup.{v}
| 0 := AddCommGroup.of (M →₀ ℤ)
| 1 := AddCommGroup.of ((finsupp.total M M ℤ id).ker)
| (n+2) := 0


/--  The boundary maps of the two step "resolution" of a module over a commutative ring. -/
def two_step_resolution_d (i j : ℕ) : two_step_resolution_X R M i ⟶ two_step_resolution_X R M j :=
match i, j with
| 1, 0 := Module.as_hom (submodule.subtype ((finsupp.total M M R id).ker))
| _, _ := 0
end


/-- The boundary maps of the two step projective resolution of an Abelian group. -/
def two_step_resolution_ab_d (M : Type v) [add_comm_group M] (i j : ℕ) :
two_step_resolution_ab_X M i ⟶ two_step_resolution_ab_X M j :=
match i, j with
| 1, 0 := AddCommGroup.of_hom (add_subgroup.subtype (finsupp.total M M ℤ id).to_add_monoid_hom.ker)
| _, _ := 0
end


/-- The two step "resolution" of a module over a commutative ring. It is a projective resolution
    if the ring is a principal ideal domain. -/
def two_step_resolution : chain_complex (Module.{max v u} R) ℕ :=
{ X := two_step_resolution_X R M,
  d := two_step_resolution_d R M,
  shape' := by {
    simp,
    rintros i j hij,
    by_cases h : i = 1 ∧ j = 0,
    { rw [h.1, h.2] at hij,
      simp only [eq_self_iff_true, not_true] at hij,
      contradiction
    },
    { push_neg at h,
      by_cases hi : i = 1,
      { have hj := h hi,
        have hj : ∃ k : ℕ, j = k + 1,
        { have h : 1 ≤ j := nat.one_le_iff_ne_zero.mpr hj,
          have h := nat.exists_eq_add_of_le h,
          simp only [add_comm] at h,
          exact h
        },
        rcases hj with ⟨k, rfl⟩,
        rw hi,
        refl
      },
      { have hi : i = 0 ∨ ∃ k : ℕ, i = k + 2 := nat.eq_zero_or_exists_eq_add_of_ne_one hi,
        cases hi with hi hi,
        { rw hi, refl },
        { rcases hi with ⟨k, rfl⟩, refl }
  }}},
  d_comp_d' := by {
    intros i j k hij hjk,
    by_cases hi : i = 1,
    { simp only [hi, complex_shape.down_rel, add_left_eq_self] at hij,
      simp only [hij, complex_shape.down_rel, nat.succ_ne_zero] at hjk,
      contradiction
    },
    { have hi : i = 0 ∨ ∃ k : ℕ, i = k + 2 := nat.eq_zero_or_exists_eq_add_of_ne_one hi,
      cases hi with hi hi,
      { rw hi, simp only [two_step_resolution_d, zero_comp]},
      { rcases hi with ⟨k, rfl⟩, simp only [two_step_resolution_d, zero_comp]}
  }}
}


/-- The two step projective resolution of an abelian group M by the free abelian group M →₀ ℤ over M
    and the kernel of the natural map (M →₀ ℤ) → M. -/
def two_step_resolution_ab  (M : Type v) [add_comm_group M] : chain_complex AddCommGroup.{v} ℕ :=
{ X := two_step_resolution_ab_X M,
  d := two_step_resolution_ab_d M,
  shape' := by {
    simp,
    rintros i j hij,
    by_cases h : i = 1 ∧ j = 0,
    { rw [h.1, h.2] at hij,
      simp only [eq_self_iff_true, not_true] at hij,
      contradiction
    },
    { push_neg at h,
      by_cases hi : i = 1,
      { have hj := h hi,
        have hj : ∃ k : ℕ, j = k + 1,
        { have h : 1 ≤ j := nat.one_le_iff_ne_zero.mpr hj,
          have h := nat.exists_eq_add_of_le h,
          simp only [add_comm] at h,
          exact h
        },
        rcases hj with ⟨k, rfl⟩,
        rw hi,
        refl
      },
      { have hi : i = 0 ∨ ∃ k : ℕ, i = k + 2 := nat.eq_zero_or_exists_eq_add_of_ne_one hi,
        cases hi with hi hi,
        { rw hi, refl },
        { rcases hi with ⟨k, rfl⟩, refl }
  }}},
  d_comp_d' := by {
    intros i j k hij hjk,
    by_cases hi : i = 1,
    { simp only [hi, complex_shape.down_rel, add_left_eq_self] at hij,
      simp only [hij, complex_shape.down_rel, nat.succ_ne_zero] at hjk,
      contradiction
    },
    { have hi : i = 0 ∨ ∃ k : ℕ, i = k + 2 := nat.eq_zero_or_exists_eq_add_of_ne_one hi,
      cases hi with hi hi,
      { rw hi, simp only [two_step_resolution_ab_d, zero_comp]},
      { rcases hi with ⟨k, rfl⟩, simp only [two_step_resolution_ab_d, zero_comp]}
  }}
}


/-- The surjective homomorphism from the two step "resolution" of a module over a commutative ring
    to the module. -/
def two_step_resolution_hom :
(two_step_resolution R M) ⟶ ((chain_complex.single₀ (Module.{max u v} R)).obj (of R M)) :=
begin
  apply (chain_complex.to_single₀_equiv (two_step_resolution R M) (of R M)).inv_fun,
  refine ⟨finsupp.total M M R id, _⟩,
  ext,
  rw category_theory.comp_apply,
  dunfold two_step_resolution,
  simp [two_step_resolution_d, Module.as_hom]
end


/-- The surjective homomorphism from the two step projective resolution of an Abelian group to the
    group. -/
def two_step_resolution_hom_ab (M : Type v) [add_comm_group M] :
(two_step_resolution_ab M) ⟶ ((chain_complex.single₀ AddCommGroup.{v}).obj (AddCommGroup.of M)) :=
begin
  apply (chain_complex.to_single₀_equiv (two_step_resolution_ab M) (AddCommGroup.of M)).inv_fun,
  refine ⟨(finsupp.total M M ℤ id).to_add_monoid_hom, _⟩,
  ext,
  rw category_theory.comp_apply,
  dunfold two_step_resolution_ab,
  simp [two_step_resolution_ab_d, AddCommGroup.of_hom]
end


/-- The two step resolution of a module over a principal ideal domain is a projective resolution. -/
theorem two_step_resolution_projective_pid [is_domain R] [is_principal_ideal_ring R] :
  (two_step_resolution R M).is_projective_resolution (of R M) (two_step_resolution_hom R M) :=
begin
  refine ⟨_, _, _, _⟩,
  { -- Projectivity.
    intro n,
    by_cases hn : n = 0,
    simp only [hn, two_step_resolution, two_step_resolution_X],
    apply_instance,

    by_cases hn' : n = 1,
    simp only [hn'],
    dsimp only [two_step_resolution, two_step_resolution_X],
    -- apply_instance,  -- fails because of universe unification issues
    apply Module.projective_of_of_projective.{u v},

    have hn : ∃ m : ℕ, n = m + 2,
    { have := nat.eq_zero_or_exists_eq_add_of_ne_one hn',
      simp only [hn, false_or] at this,
      exact this
    },
    rcases hn with ⟨m, rfl⟩,
    dsimp only [two_step_resolution, two_step_resolution_X],
    apply_instance
  },

  { -- Exactness at degree zero.
    dsimp [two_step_resolution, two_step_resolution_hom, Module.as_hom, chain_complex.to_single₀_equiv, two_step_resolution_d],
    rw Module.exact_iff,
    simp only [submodule.range_subtype]
  },

  { -- Exactness at positive degrees.
    dsimp only [two_step_resolution, Module.as_hom, auto_param_eq],
    intro n,
    by_cases hn : n = 0,
    { -- Exactness at degree one.
      rw [hn, zero_add 2, zero_add 1],
      dsimp only [two_step_resolution_d, Module.as_hom],
      haveI : mono (Module.as_hom ((finsupp.total M M R id).ker.subtype)),
      { rw Module.mono_iff_injective,
        dsimp only [Module.as_hom],
        exact submodule.injective_subtype (finsupp.total M M R id).ker
      },
      exact_mod_cast category_theory.exact_zero_mono (Module.as_hom ((finsupp.total M M R id).ker.subtype))
    },
    { -- Exactness at degrees greater than one.
      have hn : ∃ k : ℕ, n = k + 1,
      { have := nat.exists_eq_add_of_le (nat.one_le_iff_ne_zero.2 hn),
        simpa only [add_comm]
      },
      rcases hn with ⟨k, rfl⟩,
      dsimp only [two_step_resolution_d],
      apply category_theory.exact_of_zero
    }
  },
  { -- Surjectivity.
    dsimp only [two_step_resolution_hom, chain_complex.to_single₀_equiv, auto_param_eq],
    have : epi (Module.as_hom ((finsupp.total M M R id))),
    rw Module.epi_iff_surjective,
    dsimp only [Module.as_hom],
    exact finsupp.total_surjective R (function.surjective_id),
    exact this
  }
end


-- lemma coe_of' : (of R M : Type (max u v)) = M := rfl


lemma Module.coe_of'' (M : Module.{v} R) : (of R M) = M :=
begin
  cases M,
  dsimp [of, coe_sort, has_coe_to_sort.coe],
  refl
end


lemma AddCommGroup.coe_of' (M : AddCommGroup.{v}) : (AddCommGroup.of M) = M := by cases M; refl


lemma add_submonoid.injective_subtype {M : Type v} [add_comm_monoid M] (p : add_submonoid M) : function.injective p.subtype :=
subtype.coe_injective

/-- An ℤ-module considered as an Abelian group  is projective if it is projective as a ℤ-module. -/
@[instance]
lemma AddCommGroup.projective_of_Z_Module_projective (M : Module.{v} ℤ) [projective M] :
projective (AddCommGroup.of M) :=
begin
  refine ⟨_⟩,
  intros,
  let e' : (forget₂ (Module.{v} ℤ) AddCommGroup).obj (Module.of ℤ E) ⟶ (forget₂ (Module.{v} ℤ) AddCommGroup).obj (Module.of ℤ X) := e,
  let eM := full.preimage e',
  let f' : (forget₂ (Module.{v} ℤ) AddCommGroup).obj (Module.of ℤ M) ⟶ (forget₂ (Module.{v} ℤ) AddCommGroup).obj (Module.of ℤ X) := f,
  let fM := full.preimage f',
  haveI : epi eM,
  { apply faithful_reflects_epi (forget₂ (Module.{v} ℤ) AddCommGroup.{v}) _,
    rw full.witness,
    apply epi.mk,
    intros Z g h H,
    let g' : X ⟶ Z := g,
    let h' : X ⟶ Z := h,
    have H : e ≫ g' = e ≫ h' := H,
    --rw cancel_epi at H,    -- "failed to synthesize type class instance for epi e"
    rw @cancel_epi _ _ _ _ _ _ _inst_2 _ _ at H,
    exact H
  },
  haveI : projective (of ℤ M) := by rw [Module.coe_of'' ℤ M]; apply_instance,
  let pM := projective.factor_thru fM eM,
  use (forget₂ (Module.{v} ℤ) AddCommGroup).map pM,
  have hpM := projective.factor_thru_comp fM eM,
  have h : (forget₂ (Module.{v} ℤ) AddCommGroup).map (projective.factor_thru fM eM ≫ eM) = (forget₂ (Module.{v} ℤ) AddCommGroup).map fM := by simp only [hpM],
  rw functor.map_comp at h,
  simp only [full.witness] at h,
  exact h
end


/-- The two step resolution of an Abelian group is a projective resolution. -/
lemma two_step_resolution_ab_projective (M : Type v) [add_comm_group M] :
  (two_step_resolution_ab M).is_projective_resolution (AddCommGroup.of M) (two_step_resolution_hom_ab M) :=
begin
  refine ⟨_, _, _, _⟩,
  { -- Projectivity.
    intro n,
    by_cases hn : n = 0,
    simp only [hn, two_step_resolution_ab, two_step_resolution_ab_X],
    exact AddCommGroup.projective_of_Z_Module_projective (Module.of.{v} ℤ (M →₀ ℤ)),
    -- apply_instance,  -- fails

    by_cases hn' : n = 1,
    simp only [hn'],
    dsimp only [two_step_resolution_ab, two_step_resolution_ab_X],
    exact AddCommGroup.projective_of_Z_Module_projective (Module.of.{v} ℤ(finsupp.total M M ℤ id).ker),
    -- apply_instance,  -- fails

    have hn : ∃ m : ℕ, n = m + 2,
    { have := nat.eq_zero_or_exists_eq_add_of_ne_one hn',
      simp only [hn, false_or] at this,
      exact this
    },
    rcases hn with ⟨m, rfl⟩,
    dsimp only [two_step_resolution_ab, two_step_resolution_ab_X],
    apply_instance
  },

  { -- Exactness at degree zero.
    dsimp [two_step_resolution_ab, two_step_resolution_hom_ab, AddCommGroup.of_hom, chain_complex.to_single₀_equiv, two_step_resolution_ab_d],
    rw AddCommGroup.exact_iff,
    simp only [add_subgroup.subtype_range]
  },

  { -- Exactness at positive degrees.
    dsimp only [two_step_resolution, Module.as_hom, auto_param_eq],
    intro n,
    by_cases hn : n = 0,
    { -- Exactness at degree one.
      rw [hn, zero_add 2, zero_add 1],
      dsimp only [two_step_resolution_ab, two_step_resolution_ab_d, AddCommGroup.of_hom],
      haveI : mono (AddCommGroup.of_hom (add_subgroup.subtype (finsupp.total M M ℤ id).to_add_monoid_hom.ker)),
      { rw AddCommGroup.mono_iff_injective,
        dsimp only [AddCommGroup.of_hom],
        exact add_submonoid.injective_subtype _
      },
      exact_mod_cast category_theory.exact_zero_mono (AddCommGroup.of_hom (add_subgroup.subtype (finsupp.total M M ℤ id).to_add_monoid_hom.ker))
    },
    { -- Exactness at degrees greater than one.
      have hn : ∃ k : ℕ, n = k + 1,
      { have := nat.exists_eq_add_of_le (nat.one_le_iff_ne_zero.2 hn),
        simpa only [add_comm]
      },
      rcases hn with ⟨k, rfl⟩,
      dsimp only [two_step_resolution_ab, two_step_resolution_ab_d],
      apply category_theory.exact_of_zero
    }
  },
  { -- Surjectivity.
    dsimp only [two_step_resolution_hom, chain_complex.to_single₀_equiv, auto_param_eq],
    have : epi (AddCommGroup.of_hom (finsupp.total M M ℤ id).to_add_monoid_hom),
    rw AddCommGroup.epi_iff_surjective,
    dsimp only [AddCommGroup.of_hom],
    exact finsupp.total_surjective ℤ (function.surjective_id),
    exact this
  }
end
