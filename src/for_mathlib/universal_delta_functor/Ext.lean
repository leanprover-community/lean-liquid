import for_mathlib.universal_delta_functor.basic
import for_mathlib.derived.les3
import for_mathlib.derived.les_facts
import for_mathlib.derived.Ext_lemmas

open category_theory
universes v u
variables {A : Type u} [category.{v} A] [abelian A]

noncomputable theory

/-- Get an SES in `A` from a SES in `Aᵒᵖ`. -/
def short_exact_sequence.unop (S : short_exact_sequence Aᵒᵖ) : short_exact_sequence A :=
{ fst := S.trd.unop,
  snd := S.snd.unop,
  trd := S.fst.unop,
  f := S.g.unop,
  g := S.f.unop,
  mono' := infer_instance,
  epi' := infer_instance,
  exact' := S.exact'.unop }

lemma short_exact_sequence.short_exact (S : short_exact_sequence A) :
  short_exact S.f S.g :=
{ exact := S.exact' }

variables (A) [enough_projectives A]

/-- `Ext' i (-, B)` as a δ-functor. -/
def Ext_δ_functor (B : A) : Aᵒᵖ ⥤δ Ab.{v} :=
{ F := λ i, (Ext' i).flip.obj B,
  additive := infer_instance,
  δ := λ n,
  { app := λ S, by apply
      Ext'_δ B (short_exact_sequence.short_exact $ short_exact_sequence.unop S) n,
    naturality' := begin
      intros S T f,
      dsimp only [functor.comp_map],
      have := Ext'_δ_natural _ _ _ _ ((short_exact_sequence.Trd Aᵒᵖ).map f).unop _
        ((short_exact_sequence.Fst Aᵒᵖ).map f).unop _ _ B
        (short_exact_sequence.short_exact $ short_exact_sequence.unop T)
        (short_exact_sequence.short_exact $ short_exact_sequence.unop S) n,
      dsimp only [quiver.hom.op_unop] at this,
      exact this,
      exact f.snd.unop,
      dsimp only [short_exact_sequence.unop, ← unop_comp], rw f.sq2, refl,
      dsimp only [short_exact_sequence.unop, ← unop_comp], rw ← f.sq1, refl,
    end },
  mono := begin
    intros S,
    let e := bounded_derived_category.Ext'_zero_flip_iso A B,
    let t := _, change mono t,
    have ht : t = (e.hom.app _) ≫ category_theory.functor.map _ S.f ≫ (e.inv.app _),
    { dsimp [t],
      erw ← e.hom.naturality_assoc,
      rw [← nat_trans.comp_app, iso.hom_inv_id, nat_trans.id_app, category.comp_id],
      refl },
    rw ht, clear ht t,
    apply_with mono_comp { instances := ff }, apply_instance,
    apply_with mono_comp { instances := ff }, swap, apply_instance,
    apply concrete_category.mono_of_injective, intros a b h,
    dsimp at h,
    rwa ← cancel_epi S.f.unop,
  end,
  exact' := begin
    intros n S,
    have := (short_exact.Ext'_five_term_exact_seq B
      (short_exact_sequence.short_exact $ short_exact_sequence.unop S) n).extract 0 2,
    rw exact_iff_exact_seq, exact this,
  end,
  exact_δ := begin
    intros n S,
    have := (short_exact.Ext'_five_term_exact_seq B
      (short_exact_sequence.short_exact $ short_exact_sequence.unop S) n).extract 1 2,
    rw exact_iff_exact_seq, exact this,
  end,
  δ_exact := begin
    intros n S,
    have := (short_exact.Ext'_five_term_exact_seq B
      (short_exact_sequence.short_exact $ short_exact_sequence.unop S) n).extract 2 3,
    rw exact_iff_exact_seq, exact this,
  end }

.

instance (B : A) : delta_functor.tohoku.effaceable (Ext_δ_functor A B) :=
begin
  constructor, intros X n,
  let P := projective.over X.unop,
  let π : P ⟶ X.unop := projective.π _,
  constructor,
  refine ⟨_,π.op,_⟩,
  apply limits.is_zero.eq_of_tgt,
  apply bounded_derived_category.Ext'_is_zero_of_projective,
  apply_instance,
  norm_cast,
  exact nat.succ_pos n,
end

instance (B : A) : delta_functor.universal (Ext_δ_functor A B) :=
delta_functor.universal_of_effacable _
