import for_mathlib.universal_delta_functor.basic
import for_mathlib.derived.les3
import for_mathlib.derived.les_facts

open category_theory
universes v u
variables {A : Type u} [category.{v} A] [abelian A] [enough_projectives A]

noncomputable theory

def short_exact_sequence.unop (S : short_exact_sequence Aᵒᵖ) : short_exact_sequence A :=
{ fst := S.trd.unop,
  snd := S.snd.unop,
  trd := S.fst.unop,
  f := S.g.unop,
  g := S.f.unop,
  mono' := infer_instance,
  epi' := infer_instance,
  exact' := S.exact'.unop }

def short_exact_sequence.short_exact (S : short_exact_sequence A) :
  short_exact S.f S.g :=
{ exact := S.exact' }

variable (A)

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
  mono := sorry,
  exact' := sorry,
  exact_δ := sorry,
  δ_exact := sorry }
