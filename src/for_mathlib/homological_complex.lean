import data.matrix.notation

import for_mathlib.short_exact_sequence

noncomputable theory

open category_theory
open category_theory.limits

universes v u

namespace homological_complex

variables (C : Type u) [category.{v} C] [abelian C]
variables {ι : Type*} {c : complex_shape ι}

abbreviation Fst : chain_complex (short_exact_sequence C) ℕ ⥤
  homological_complex C (complex_shape.down ℕ) :=
(short_exact_sequence.Fst C).map_homological_complex _

abbreviation Snd : chain_complex (short_exact_sequence C) ℕ ⥤
  homological_complex C (complex_shape.down ℕ) :=
(short_exact_sequence.Snd C).map_homological_complex _

abbreviation Trd : chain_complex (short_exact_sequence C) ℕ ⥤
  homological_complex C (complex_shape.down ℕ) :=
(short_exact_sequence.Trd C).map_homological_complex _

abbreviation Fst_Snd : Fst C ⟶ Snd C :=
nat_trans.map_homological_complex (short_exact_sequence.f_nat C) _

abbreviation Snd_Trd : Snd C ⟶ Trd C :=
nat_trans.map_homological_complex (short_exact_sequence.g_nat C) _

variables {C}

variables (A : chain_complex (short_exact_sequence C) ℕ)

instance Fst_Snd_mono (n : ℕ) : mono (((Fst_Snd C).app A).f n) := (A.X n).mono'

instance Snd_Trd_epi (n : ℕ) : epi (((Snd_Trd C).app A).f n) := (A.X n).epi'

instance Fst_Snd_Trd_exact (n : ℕ) : exact (((Fst_Snd C).app A).f n) (((Snd_Trd C).app A).f n) :=
(A.X n).exact'

end homological_complex
