import condensed.exact
import for_mathlib.split_exact

noncomputable theory

universe u

open opposite category_theory

namespace Condensed

lemma mono_iff_ExtrDisc {A B : Condensed.{u} Ab.{u+1}} (f : A ⟶ B) :
  mono f ↔ ∀ S : ExtrDisc, mono (f.1.app $ ExtrDisc_to_Profinite.op.obj (op S)) :=
begin
  split,
  { intros H S,
    erw (abelian.tfae_mono (A.val.obj (op S.val)) (f.val.app (op S.val))).out 0 2,
    erw (abelian.tfae_mono A f).out 0 2 at H,
    rw Condensed.exact_iff_ExtrDisc at H,
    apply H, },
  { intro H,
    apply exact.mono_of_exact_zero_left, swap, exact A,
    rw Condensed.exact_iff_ExtrDisc,
    intro S, specialize H S,
    show exact 0 _,
    erw (abelian.tfae_mono (A.val.obj (op S.val)) (f.val.app (op S.val))).out 2 0,
    exact H, }
end

lemma short_exact_iff_ExtrDisc {A B C : Condensed.{u} Ab.{u+1}} (f : A ⟶ B) (g : B ⟶ C) :
  short_exact f g ↔ ∀ S : ExtrDisc, short_exact
      (f.1.app $ ExtrDisc_to_Profinite.op.obj (op S))
      (g.1.app $ ExtrDisc_to_Profinite.op.obj (op S)) :=
begin
  split,
  { intros H S,
    apply_with short_exact.mk {instances:=ff},
    { revert S, rw ← mono_iff_ExtrDisc, exact H.mono, },
    { rw AddCommGroup.epi_iff_surjective,
      revert S, erw ← is_epi_iff_forall_surjective, exact H.epi, },
    { revert S, rw ← Condensed.exact_iff_ExtrDisc, exact H.exact } },
  { intro H,
    apply_with short_exact.mk {instances:=ff},
    { rw mono_iff_ExtrDisc, intro S, exact (H S).mono, },
    { simp only [is_epi_iff_forall_surjective, ← AddCommGroup.epi_iff_surjective],
      intro S, exact (H S).epi, },
    { rw Condensed.exact_iff_ExtrDisc, intro S, exact (H S).exact } }
end

end Condensed
