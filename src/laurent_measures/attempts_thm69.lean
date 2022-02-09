import clean

open nnreal finset
open_locale nnreal classical big_operators topological_space


--lemma my_sum_0 {f : ℤ → ℝ} :
--  summable (λ n : {z : ℤ // 0 ≤ z}, f n) ↔ summable (λ n : ℕ, f n) :=
--begin
--  sorry,
--  --refine ⟨λ h, _, λ h, _⟩,
----  apply summable.subtype,
--end
--#check subtype.heq_iff_coe_eq
--#check eq_rec_heq
--have : {z // z ∉ {z : ℤ | 0 ≤ z}} = {z // z ∈ {z : ℤ | z < 0}}, { simp },


/-  The map `x ↦ x - N` is an equivalence between `{x : ℤ // N ≤ x}` and `{x : ℤ // 0 ≤ x}`.
def equiv_bdd_integer_nat_1 (N : ℤ) : {x // N ≤ x} ≃ {x : ℤ // 0 ≤ x} :=
equiv_subtype_le_add N
 -/

/--  The subtype of nonnegative integers is equivalent to the natural number. -/
def equiv.int_subtype_nonneg_nat : {x : ℤ // 0 ≤ x} ≃ ℕ :=
int_subtype_nonneg_equiv

@[simp]
lemma equiv.int_subtype_nonneg_nat_eval {z : {x : ℤ // 0 ≤ x}} :
  (equiv.int_subtype_nonneg_nat z : ℤ) = z :=
int_subtype_nonneg_equiv_eval

lemma int.nonneg_zero : int.nonneg 0 :=
by cases int.nonneg_or_nonneg_neg 0 with k k; exact k

lemma int.le_compl_eq (d : ℤ) : {z : ℤ | d ≤ z}ᶜ = {z : ℤ | z < d} :=
by { ext, simp }

lemma int.le_eq_compl (d : ℤ) : {z : ℤ | d ≤ z} = {z : ℤ | z < d}ᶜ :=
by { ext, simp }

lemma heqheq {α : Type*} (f : ℤ → α) :
  (λ (n : {z : ℤ // z ∉ {z : ℤ | 0 ≤ z}}), f ↑n) == (λ (n : {z : ℤ // z < 0}), f n) :=
function.hfunext (by simp only [not_le, set.mem_set_of_eq])
  (λ a a' aa, heq_of_eq (congr_arg f ((subtype.heq_iff_coe_eq (by simp)).mp aa)))

section topological_space
variables {α : Type*} [topological_space α] [add_comm_monoid α] {f : ℤ → α}

lemma conv_ty {P : ℤ → Prop} :
  summable (λ n : { z | P z }, f n) ↔ summable (λ n : { z // P z }, f n) :=
summable_congr (congr_fun rfl)

lemma my_sum_2 :
  summable (λ n : {z : ℤ | z < 0}, f n) ↔ summable (λ n : {z : ℤ | 0 < z}, f (- n)) :=
begin
  convert (equiv.neg_gt_zero ℤ).summable_iff,
  ext,
  simp only [equiv.neg_gt_zero_eval, eq_self_iff_true, function.comp_app, neg_neg],
end

lemma my_sum_2_st :
  summable (λ n : {z : ℤ // z < 0}, f n) ↔ summable (λ n : {z : ℤ // 0 < z}, f (- n)) :=
my_sum_2

lemma my_sum_3 :
  summable (λ n : {z : ℤ | 0 ≤ z}, f n) ↔ summable (λ n : ℕ, f n) :=
begin
  convert equiv.summable_iff (int_subtype_nonneg_equiv),
  ext,
  simp only [eq_self_iff_true, function.comp_app, int_subtype_nonneg_equiv_eval],
end

end topological_space

section uniform
variables {α : Type*} [uniform_space α] [add_comm_group α] [uniform_add_group α] [complete_space α]
variable {f : ℤ → α}

lemma my_sum :
  summable f ↔ summable (λ n : {z : ℤ | 0 ≤ z}, f n) ∧ summable (λ n : {z : ℤ | 0 ≤ z}ᶜ, f n) :=
summable_subtype_and_compl.symm

lemma my_sum_st :
  summable f ↔ summable (λ n : {z : ℤ // 0 ≤ z}, f n) ∧ summable (λ n : {z : ℤ // z < 0}, f n) :=
begin
  rw my_sum,
  refine ⟨_, _⟩; rintros ⟨h1, h2⟩; refine ⟨h1, _⟩,
  { refine (equiv.summable_iff compl_le).mp _,
    convert h2 using 1,
    funext x,
    cases x with x hx,
    simp only [equiv.coe_fn_mk, compl_le.equations._eqn_1, function.comp_app, subtype.coe_mk] },
  { have : summable (λ (n : {z : ℤ // z < 0}), f n) ↔
      summable (λ (n : {z : ℤ // z ∉ {z : ℤ | 0 ≤ z}}), f n),
    { convert iff.rfl,
      { simp },
      { exact heqheq _ } },
    exact conv_ty.mpr (this.mp h2) }
end

lemma my_sum_1 :
  summable f ↔ summable (λ n : {z : ℤ | 0 ≤ z}, f n) ∧ summable (λ n : {z : ℤ | z < 0}, f n) :=
begin
  rw [← compl_compl {z : ℤ | z < 0}, ← int.le_eq_compl],
  exact my_sum
end

lemma my_sum_1_st :
  summable f ↔ summable (λ n : {z : ℤ // 0 ≤ z}, f n) ∧ summable (λ n : {z : ℤ // z < 0}, f n) :=
my_sum_1

def equiv_bdd_integer_nat_3 (N : ℤ) : {x // N ≤ x} ≃ ℕ :=
(equiv_subtype_le_add N).trans equiv.int_subtype_nonneg_nat

@[simp]
lemma bdd_eval {d : ℤ} {n : ℕ} : ((equiv_bdd_integer_nat d) n : ℤ) = n + d := rfl

@[simp]
lemma bdd_eval_symm (d : ℤ) (x : { z : ℤ // d ≤ z}) :
  ((equiv_bdd_integer_nat d).symm x : ℤ) = x - d :=
begin
  cases x with x hx,
  have : ∃ y : ℕ, x - d = y,
  { lift (x - d) to ℕ using (sub_nonneg.mpr hx) with r,
    exact ⟨_, rfl⟩ },
  cases this with y hy,
  rw [subtype.coe_mk, hy, int.coe_nat_inj'],
  refine (equiv_bdd_integer_nat d).injective (subtype.coe_injective _),
  simp [ ← hy],
end

lemma my_sum_4 :
  summable f → summable (λ n : ℕ, f n) :=
λ sf, by convert (equiv_bdd_integer_nat 0).summable_iff.mpr (my_sum_1_st.mp sf).1


def eq_eq_eq {α β γ : Type*} (f : α ≃ β) (g : β ≃ γ) : α ≃ γ :=
f.trans g

def oppo : ({z : ℤ | 0 ≤ z}ᶜ : set ℤ) ≃ ℕ :=
compl_le.trans $ (equiv.neg_gt_zero ℤ).trans ((equiv_subtype_le_add _).trans equiv.int_subtype_nonneg_nat)
--(equiv_bdd_integer_nat 1).symm

@[simp]
lemma oppo_symm_eval {n : ℕ} : (oppo.symm n : ℤ) = - n - 1 :=
by simp [oppo, equiv.int_subtype_nonneg_nat, equiv_subtype_le_add, equiv.neg_gt_zero, compl_le, neg_add_eq_sub]

lemma my_sum_5 :
  summable f ↔ summable (λ n : ℕ, f n) ∧ summable (λ n : ℕ, f (- n - 1)) :=
begin
  refine (@summable_subtype_and_compl α _ _ _ _ _ _ {z : ℤ | 0 ≤ z}).symm.trans _,
  rw ← equiv.summable_iff equiv.int_subtype_nonneg_nat,
  rw ← equiv.summable_iff oppo.symm,
  refine ⟨_, _⟩;
  rintro ⟨h1, h2⟩;
  refine ⟨_, _⟩;
  exact summable.congr ‹_› (λ b, by simp),
--  try { exact summable.congr h2 (λ b, by simp) },
--  exact summable.congr h1 (λ b, by simp only [function.comp_app, equiv.int_subtype_nonneg_nat_eval]),
--  refine summable.congr h1 (λ b, _),
--  simp only [equiv.int_subtype_nonneg_nat_eval, function.comp_app],
--  refine summable.congr h2 (λ b, _),
--  simp only [oppo_symm_eval, function.comp_app],
end


lemma my_sum_5 :
  summable f ↔ summable (λ n : ℕ, f n) ∧ summable (λ n : ℕ, f (- n - 1)) :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { refine ⟨my_sum_4 h, _⟩,
    obtain F := (my_sum_1_st.mp h).2,
    rw my_sum_2_st at F,
    --change' summable (λ (n : {z : ℤ // 1 ≤ z}), f (-↑n)) at F,
    convert (equiv_bdd_integer_nat 1).summable_iff.mpr F,
    ext x,
    rw [function.comp_app, bdd_eval, neg_add, sub_eq_add_neg] },
  { cases h with h1 h2,
    refine my_sum_1.mpr ⟨my_sum_3.mpr h1, _⟩,
    rw my_sum_2,
    --change summable (λ (n : {z : ℤ | 1 ≤ z}), f (-↑n)),
    convert (equiv_bdd_integer_nat 1).symm.summable_iff.mpr h2,
    ext ⟨x, hx⟩,
    rw [function.comp_app, bdd_eval_symm, neg_sub, sub_sub_cancel_left] }
end

lemma aux_summable_iff_on_nat'_1 {f : ℤ → α} (d : ℤ) (h : ∀ n : ℤ, n < d → f n = 0) :
  summable (λ n, f n) ↔ summable (λ n : ℕ, f (n + d)) :=
begin
  have : summable (λ (n : ℕ), f (-↑n - 1)),
  { by_cases d0 : - d < 0,
    { convert summable_zero,
      refine funext (λ (x : ℕ), h _ (lt_trans _ (neg_lt_zero.mp d0))),
      exact sub_neg.mpr (lt_of_le_of_lt (neg_nonpos.mpr (int.coe_zero_le x)) zero_lt_one) },
    { lift - d to ℕ using (not_lt.mp d0) with d1 hd1,
      refine summable_of_ne_finset_zero (λ b (hb : b ∉ range d1), h _ _),
      rw [← neg_lt_neg_iff, neg_sub, ← hd1, sub_neg_eq_add, ← int.coe_nat_one],
      refine (int.coe_nat_lt_coe_nat_iff _ _).mpr (nat.lt_one_add_iff.mpr _),
      exact not_lt.mp (λ hh, hb (mem_range.mpr hh)) } },
  rw [int_summable_iff],
  simp [this],
  refine ⟨λ h, _, λ h, _⟩,


  rw [← neg_add', neg_lt, ← sub_lt_iff_lt_add, ← not_le],
end

#exit

lemma aux_summable_iff_on_nat'_1 {f : ℤ → α} (d : ℤ) (h : ∀ n : ℤ, n < d → f n = 0) :
  summable (λ n, f n) ↔ summable (λ n : ℕ, f (n + d)) :=
begin
  rw my_sum_5,
  have : summable (λ (n : ℕ), f (-↑n - 1)),
  { by_cases d0 : - d < 0,
    { convert summable_zero,
      refine funext (λ (x : ℕ), h _ (lt_trans _ (neg_lt_zero.mp d0))),
      exact sub_neg.mpr (lt_of_le_of_lt (neg_nonpos.mpr (int.coe_zero_le x)) zero_lt_one) },
    { lift - d to ℕ using (not_lt.mp d0) with d1 hd1,
      apply summable_of_ne_finset_zero,
      rintros b (hb : b ∉ range d1),
      apply h,
      simp at hb,
      linarith } },
  simp [this],
  refine ⟨λ h, _, λ h, _⟩,

  rw [← neg_add', neg_lt, ← sub_lt_iff_lt_add, ← not_le],
end


lemma my_sum_6 :
  summable (λ n : ℕ, f (- n)) ↔ summable (λ n : ℕ, f (- n - 1)) :=
begin
  refine ⟨λ h, _, λ h, _⟩,


end

#exit
  ext x,
  cases x with x hx,
  simp,
  apply congr_arg,
  apply neg_eq_iff_neg_eq.mp,
  simp,rw add_comm,
  rw bdd_eval_symm,
  suffices : x + 1 + (-1) = x,convert this,simp [(equiv_bdd_integer_nat 1)],
  rw neg_neg,
  refine ⟨λ h, _, λ h, _⟩,
  cases x with x hx,
  simp,
  refine my_sum_1_st.trans _,
  refine ⟨_, _⟩; rintros ⟨h1, h2⟩,
  --refine ⟨h1, _⟩,

  refine ⟨λ h, ⟨my_sum_4 h, _⟩, λ h, _⟩,

end

end uniform

--def eq_sh (d : ℤ) : {z : ℤ // d ≤ z} ≃ ℕ := (equiv_bdd_integer_nat d).symm

lemma my_sum_3_d {f : ℤ → ℝ} (d : ℤ) :
  summable (λ n : {z : ℤ | d ≤ z}, f n) ↔ summable (λ n : ℕ, f n) :=
begin
  rw ← my_sum_3,

  rw ← summable_shift,
  refine ⟨λ h, _, λ h, _⟩,

end


--lemma inj_inj {α β : Type*} (f : α → ℝ) (g : β → ℝ) (fi : function.injective f)
--  (gi : function.injective g) : (∀ )

lemma my_sum_4 {f : ℤ → ℝ} :
  summable f ↔ summable (λ n : ℕ, f n) ∧ summable (λ n : ℕ, f (- n)) :=
begin
  rw my_sum_1,
  rw my_sum_2,
  rw my_sum_3,
  refine ⟨_, _⟩; rintros ⟨h1, h2⟩; refine ⟨h1, _⟩,
  have : summable (λ (n : {z : ℤ | 0 < z}), f (- n)) ↔ summable (λ (n : {z : ℤ | 1 ≤ z}), f (- n)),
  { exact iff.rfl },
  rw [this, ← equiv.summable_iff (equiv_bdd_integer_nat 1)] at h2,
  refine summable_comp_injective _ _,
  exact h2,
  rw ← equiv.summable_iff (equiv_bdd_integer_nat 1).symm,

end

#exit
lemma my_sum_3 {f : ℤ → ℝ} :
  summable (λ n : {z : ℤ | 0 < z}, f n) ↔ summable (λ n : {z : ℤ | 0 ≤ z}, f n) :=
begin
  rw equiv.summable_iff (equiv_bdd_integer_nat 0).symm,
  simp_rw equiv_bdd_integer_nat 0,
  refine ⟨λ h, _, λ h, _⟩,
  have z0 : (0 : ℤ) ∈ {z : ℤ | 0 ≤ z}, simp,
  have zc : ({ z : {z : ℤ | 0 ≤ z} // z ≠ ⟨_, z0⟩}) ≃ {z : ℤ | 0 < z},
  refine ⟨by {
    rintro ⟨⟨z, hz⟩, hz0⟩,
    refine ⟨z, _⟩,
    rw set.mem_set_of_eq at ⊢ hz,
    apply lt_of_le_of_ne hz _,
    rw [ne.def, subtype.mk_eq_mk] at hz0,
    exact ne.symm hz0 }, by {
      rintro ⟨z, hz0⟩,
    rw set.mem_set_of_eq at hz0,
    refine ⟨⟨z, _⟩, _⟩,
    exact hz0.le,
    simp [hz0.ne'] }
, _, _⟩,

  convert summable.add_compl h _ using 0,
  rw zero_zero.eval f,
  exact (zero_zero ℤ).summable_iff
end

lemma my_sum_3 {f : ℤ → ℝ} :
  summable (λ n : {z : ℤ | 0 < z}, f n) ↔ summable (λ n : ℕ, f n) :=
begin

  rw zero_zero.eval f,
  exact (zero_zero ℤ).summable_iff
end

#exit
,
  ext,
  simp,
  refine ⟨λ h h0, _, λ h, _⟩,
  rcases int.nonneg.elim h0 with ⟨w, rfl⟩,
  exact not_le.mpr h (int.coe_zero_le w),
  cases x.nonneg_or_nonneg_neg with k k,
  refine (h k).elim,
  cases int.nonneg.elim k with w hw,
  rw neg_eq_iff_neg_eq at hw,
  subst hw,
  refine neg_lt.mp _,
  simp,
  apply zero_lt_iff.mpr,
  rintro rfl,
  exact h int.nonneg_zero,
ext,simp,
  simp at h,
  have : 0 ≤ -x,
  any_goals { apply_instance },

  rw ← mem_def at h0,
  refine ⟨λ h, ⟨h.subtype _, h.subtype _⟩, _⟩,
  rintro ⟨hp, hm⟩,
  have : summable (f ∘ (coe : {z : ℤ | 0 ≤ z} → ℤ)) := hp,
  refine summable.add_compl hp _,

  convert hm using 0,
  simp,

  refine ⟨λ h, _, λ h, _⟩,
  convert h using 0,
  convert congr_arg summable _,
  simp,ext,
  refine ⟨λ h, _, λ h, _⟩,
  unfold int.nonneg at h,

  have : summable (f ∘ (coe : {z : ℤ | 0 < z} → ℤ)) := hp,

--  set f' : ℕ → ℝ := f ∘ coe with hf,
--  have : f' = (λ (n : ℕ), f ↑n),ext,simp,
--  exact hp,
--  rw [← this, hf] at hp,


  convert hp,
  sorry,
  apply summable.add_compl this,
  convert this,
end

#exit
lemma sum_range_sum_Icc_3 {α : Type*} [field α] (f : ℤ → α) {n d : ℤ} (m : ℕ) (hn : n - d = m) :
  ∑ l in (range m.succ), (f (n - l)) * 2 ^ l = ∑ k in (Icc d n), (f k) * 2 ^ (n - k) :=
begin
  have sum_swap : ∑ (l : ℕ) in range m.succ, f (n - l) * 2 ^ l =
    ∑ (l : ℕ) in range m.succ, f (l + d) * 2 ^ (m - l),
  { convert (sum_reverse (λ l, f (n - l) * 2 ^ l) m).symm using 1,
    { simp_rw ← zpow_coe_nat },
    refine sum_congr rfl (λ x hx, _),
    congr' 1,
    { rw [sub_sub_assoc_swap, add_comm n, add_sub_assoc],
      exact congr_arg f ((add_right_inj _).mpr (eq_sub_iff_add_eq.mpr (eq_sub_iff_add_eq'.mp hn.symm))) },
    { simp only [← zpow_of_nat, int.of_nat_eq_coe, ← int.sub_nat_nat_eq_coe, int.sub_nat_nat_of_le
        (nat.lt_succ_iff.mp (mem_range.mp hx))] } },
  rw [sum_swap, ← sum_finset_coe, ← sum_finset_coe _ (Icc _ _)],
  refine fintype.sum_equiv (range_equiv_Icc_1 _ hn) _ _ (λ x, _),
  dsimp [range_equiv_Icc_1],
  rw [← sub_sub, sub_right_comm, ← zpow_coe_nat],
  refine congr_arg ((*) _) (congr_arg (pow 2) _),
  convert (@nat.cast_sub ℤ _ _ _ _ (mem_range_succ_iff.mp x.2)).trans _ using 1;
  simp only [hn, int.nat_cast_eq_coe_nat, subtype.val_eq_coe],
end

#exit

/-
def range_equiv_Icc_1 {n d : ℤ} (m : ℕ) (hm : n - d = m) :
  range m.succ ≃ (Icc d n) :=
begin
  refine ⟨λ a, ⟨a + d, mem_Icc.mpr ⟨_, _⟩⟩, _, _, _⟩,
  { exact (le_add_iff_nonneg_left _).mpr (int.of_nat_nonneg _) },
  { refine add_le_of_le_sub_right _,
    exact (int.coe_nat_le.mpr (nat.le_of_lt_succ $ (@mem_range m.succ a).mp a.2)).trans hm.ge },
  { rintro ⟨a, hha⟩,
    refine ⟨(a - d).nat_abs, mem_range_succ_iff.mpr _⟩,
    lift (a - d) to ℕ using (sub_nonneg.mpr ((mem_Icc).mp hha).1) with ad had,
    rw [int.nat_abs_of_nat, ← (int.coe_nat_le_coe_nat_iff _ _), had, ← hm],
    exact sub_le_sub_right ((mem_Icc).mp hha).2 _ },
  { exact λ x, subtype.ext (by simp) },
  { rintro ⟨x, hx⟩,
    simp [int.nat_abs_of_nonneg (sub_nonneg.mpr (mem_Icc.mp hx).1), sub_add_cancel] }
end

def range_equiv_Icc {n d : ℤ} (hn : 0 ≤ n - d) :
  range (int.eq_coe_of_zero_le hn).some.succ ≃ (Icc d n) :=
range_equiv_Icc_1 _ (Exists.some_spec (int.eq_coe_of_zero_le hn))
-/

lemma sum_reverse {β : Type*} [add_comm_group β] (f : ℤ → β) (n : ℕ) :
  ∑ l in (range n.succ), (f (n - l)) = ∑ l in (range n.succ), f l :=
begin
  induction n with n hn generalizing f,
  { simp only [zero_sub, int.coe_nat_zero, sum_singleton, neg_zero, range_one] },
  { rw [sum_range_succ', sum_range_succ (f ∘ coe)],
    simp only [←hn, int.coe_nat_zero, add_sub_add_right_eq_sub, function.comp_app, sub_zero,
      int.coe_nat_succ] }
end

noncomputable
def equiv_bdd_integer_nat_1 (N : ℤ) : ℕ ≃ {x // N ≤ x} :=
begin
  fconstructor,
  { refine λ n, ⟨n + N, le_add_of_nonneg_left (int.coe_nat_nonneg n)⟩ },
  { rintro ⟨x, hx⟩,
    exact (int.eq_coe_of_zero_le (sub_nonneg.mpr hx)).some },
  { intro a,
    simp_rw [add_tsub_cancel_right],
    exact (int.coe_nat_inj $ Exists.some_spec $ int.eq_coe_of_zero_le $ int.of_nat_nonneg a).symm },
  { rintro ⟨_, hx⟩,
    refine subtype.ext (add_eq_of_eq_sub _),
    exact ((int.eq_coe_of_zero_le (sub_nonneg.mpr hx)).some_spec).symm }
end



lemma sum_range_sum_Icc_2 (f : ℤ → ℝ) (n d : ℤ) (m : ℕ) (hm : n - d = m) :
  ∑ l in (range m.succ), (f (n - l)) * 2 ^ l = ∑ k in (Icc d n), (f k) * 2 ^ (n - k) :=
begin
--  lift n-d to ℕ using hn with m hm,
--  set m : ℕ := (int.eq_coe_of_zero_le hn).some,
  have sum_swap : ∑ (l : ℕ) in range m.succ, (f (n - l) : ℝ) * 2 ^ l =
    ∑ (l : ℕ) in range m.succ, (f (l + d) : ℝ) * 2 ^ (m - l),
  { convert (sum_reverse (λ l, (f (n - l) : ℝ) * 2 ^ l) m).symm using 1,
    refine sum_congr rfl (λ x hx, _),
    congr' 1,
    { rw [sub_sub_assoc_swap, add_comm n, add_sub_assoc],
      exact congr_arg f ((add_right_inj _).mpr (eq_sub_iff_add_eq.mpr (eq_sub_iff_add_eq'.mp hm.symm))) },
    { simp only [← zpow_of_nat, int.of_nat_eq_coe, ← int.sub_nat_nat_eq_coe, int.sub_nat_nat_of_le
        (nat.lt_succ_iff.mp (mem_range.mp hx))] } },
--  have im : (int.eq_coe_of_zero_le hn).some = m,
--  { rw (int.coe_nat_eq_coe_nat_iff _ _).mp (int.eq_coe_of_zero_le (int.coe_zero_le m)).some_spec,
--    simp_rw [← hm] },
  rw [sum_swap],
  nth_rewrite_lhs 0 [← sum_finset_coe],
  nth_rewrite_rhs 0 [← sum_finset_coe],
--  rw ← im,
  have hn : 0 ≤ n - d,sorry,
  refine fintype.sum_equiv (range_equiv_Icc_1 _ hm) _ _ _,
  intro x,
  dsimp [range_equiv_Icc],
  apply_rules [mul_eq_mul_left_iff.mpr, or.intro_left],
  rw [← zpow_coe_nat],
  apply congr_arg,
  cases x with x hx,
  dsimp,
  norm_cast,
  have := @nat.cast_sub ℤ _ _ _ _ (mem_range_succ_iff.mp hx),
  convert this.trans _,funext,sorry,
  rw ← hm,
--  obtain F := int.eq_coe_of_zero_le _,
--  simp only [*, int.nat_cast_eq_coe_nat, sub_left_inj, subtype.val_eq_coe],
--  simpa only [*, int.nat_cast_eq_coe_nat, sub_left_inj, subtype.val_eq_coe],
end

lemma sum_range_sum_Icc_1 (f : ℤ → ℝ) (n d : ℤ) (hn : 0 ≤ n - d) :
 ∑ l in (range (int.eq_coe_of_zero_le hn).some.succ), (f (n - l)) * 2 ^ l =
 ∑ k in (Icc d n), (f k) * 2 ^ (n - k) :=
begin
  lift n-d to ℕ using hn with m hm,
--  set m : ℕ := (int.eq_coe_of_zero_le hn).some,
  have sum_swap : ∑ (l : ℕ) in range m.succ, (f (n - l) : ℝ) * 2 ^ l =
    ∑ (l : ℕ) in range m.succ, (f (l + d) : ℝ) * 2 ^ (m - l),
  { convert (sum_reverse (λ l, (f (n - l) : ℝ) * 2 ^ l) m).symm using 1,
    refine sum_congr rfl (λ x hx, _),
    congr' 1,
    { rw [sub_sub_assoc_swap, add_comm n, add_sub_assoc],
      exact congr_arg f ((add_right_inj _).mpr (eq_sub_iff_add_eq.mpr (eq_sub_iff_add_eq'.mp hm))) },
    { simp only [← zpow_of_nat, int.of_nat_eq_coe, ← int.sub_nat_nat_eq_coe, int.sub_nat_nat_of_le
        (nat.lt_succ_iff.mp (mem_range.mp hx))] } },
  have im : (int.eq_coe_of_zero_le hn).some = m,
  { rw (int.coe_nat_eq_coe_nat_iff _ _).mp (int.eq_coe_of_zero_le (int.coe_zero_le m)).some_spec,
    simp_rw [← hm] },
  rw [im, sum_swap],
  nth_rewrite_lhs 0 [← sum_finset_coe],
  nth_rewrite_rhs 0 [← sum_finset_coe],
--  rw ← im,
  apply fintype.sum_equiv (range_equiv_Icc hn),
  intro x,
  dsimp [range_equiv_Icc],
  apply_rules [mul_eq_mul_left_iff.mpr, or.intro_left],
  rw [← sub_sub, sub_right_comm, ← zpow_coe_nat],
  apply congr_arg,
  have := @nat.cast_sub ℤ _ _ _ _ (mem_range_succ_iff.mp x.2),
  simpa only [*, int.nat_cast_eq_coe_nat, sub_left_inj, subtype.val_eq_coe],
end


lemma sum_swap (f : ℤ → ℝ) (m : ℕ) :
  in ∑ (l : ℕ) in range m.succ, f (m - l) * 2 ^ l =
       ∑ (l : ℕ) in range m.succ, f l * 2 ^ (m - l) :=
begin
  convert (sum_reverse (λ l, (f (n - l) : ℝ) * 2 ^ l) m).symm using 1,
    refine sum_congr rfl (λ x hx, _),
    congr' 1,
    { rw [sub_sub_assoc_swap, add_comm n, add_sub_assoc],
      refine congr_arg f ((add_right_inj _).mpr (eq_sub_iff_add_eq.mpr (eq_sub_iff_add_eq'.mp _))),
      sorry },
    { simp only [← zpow_of_nat, int.of_nat_eq_coe, ← int.sub_nat_nat_eq_coe, int.sub_nat_nat_of_le
        (nat.lt_succ_iff.mp (mem_range.mp hx))] }
end

#exit
import algebra.ordered_group

lemma pro {α : Type*} [comm_group α] [linear_order α] [covariant_class α α (*) (≤)] (a b c d : α)
  (ab : a = b) (bc : b = c) (cd : c = d) : a = d :=
begin
  gpft
end


#exit
import system_of_complexes.basic

universe variables u

noncomputable theory
open_locale nnreal
open category_theory opposite normed_group_hom system_of_complexes

variables (M M' N : system_of_complexes.{u}) (f : M ⟶ M') (g : M' ⟶ N)

set_option profiler true
/-- The normed snake lemma, weak version. See Proposition 9.10 from Analytic.pdf -/
--TODO Add the non weak version for complete system of complexes
lemma weak_normed_snake {k k' k'' K K' K'' : ℝ≥0}
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')] [hk'' : fact (1 ≤ k'')]
  {m : ℕ} {c₀ : ℝ≥0}
  (hM : M.is_weak_bounded_exact k K (m+1) c₀)
  (hM' : M'.is_weak_bounded_exact k' K' (m+1) c₀)
  (hM'_adm : M'.admissible)
  (hf : ∀ c i, (f.apply : M c i ⟶ M' c i).norm_noninc)
  (Hf : ∀ (c : ℝ≥0) [fact (c₀ ≤ c)] (i : ℕ) (hi : i ≤ m+1+1) (x : M (k'' * c) i),
    ∥(res x : M c i)∥ ≤ K'' * ∥f x∥)
  (hg : ∀ c i, (g.apply : M' c i ⟶ N c i).ker = f.apply.range)
  (hgquot : system_of_complexes.is_quotient g) :
  N.is_weak_bounded_exact (k''*k*k') (K'*(K*K'' + 1)) m c₀ :=
begin
  introsI c hc i hi,
  let c₁ := k'' * (k * (k' * c)),
  suffices : ∀ n : N c₁ i, ∀ ε > 0,
    ∃ i₀ (hi₀ : i₀ = i - 1) (y : N c i₀),
      ∥res n - N.d _ _ y∥ ≤ K' * (K * K'' + 1) * ∥N.d i (i+1) n∥ + ε,
  { dsimp [c₁] at this,
    intros n₁ ε hε,
    haveI hc : fact (k'' * k * k' * c = c₁) :=
      { out := (mul_assoc _ _ _).trans ((mul_assoc _ _ _).trans rfl) },
    rcases this (res n₁) ε hε with ⟨i₀, hi₀, y, hy⟩,
    rw [res_res, d_res] at hy,
    refine ⟨i₀, _, hi₀, rfl, _⟩,
    refine ⟨y, hy.trans (add_le_add_right (mul_le_mul_of_nonneg_left _ _) ε)⟩,
    { apply (admissible_of_quotient hgquot hM'_adm).res_norm_noninc },
    { exact (nnreal.zero_le_coe : 0 ≤ K' * (K * K'' + 1)) } },
  intros n ε hε,
  let ε₁ := ε/(K' * (K * K'' + 2) + 1),

  have hε₁ : 0 < ε₁ :=
    div_pos hε (lt_of_lt_of_le zero_lt_one (nnreal.one_le_add'.out : 1 ≤ K' * (K * K'' + 2) + 1)),

  obtain ⟨m' : M' c₁ i, rfl : g m' = n⟩ := (hgquot _ _).surjective _,
  let m₁' := M'.d i (i+1) m',
  have hm₁' : g m₁' = N.d i (i+1) (g m') := (d_apply _ _ g m').symm,
  obtain ⟨m₁'' : M' c₁ (i+1),
          hgm₁'' : g m₁'' = N.d i (i+1) (g m'),
          hnorm_m₁'' : ∥m₁''∥ < ∥N.d i (i+1) (g m')∥ + ε₁⟩ :=
    (hgquot _ _).norm_lift hε₁ (N.d i (i+1) (g m')),
  obtain ⟨m₁, hm₁⟩ : ∃ m₁ : M c₁ (i+1), f m₁ + m₁'' = m₁',
  { have hrange : m₁' - m₁'' ∈ f.apply.range,
    { rw [← hg _ _, mem_ker  _ _, normed_group_hom.map_sub],
      change g m₁' - g m₁'' = 0,
      rw [hm₁', hgm₁'', sub_self] },
    obtain ⟨m₁, hm₁ : f m₁ = m₁' - m₁''⟩ := (mem_range _ _).1 hrange,
    exact ⟨m₁, by rw [hm₁, sub_add_cancel]⟩ },

  have him : i+2 ≤ m+2 := add_le_add_right hi _,
  have hm₂ : f (M.d (i+1) (i+2) m₁) = -M'.d (i+1) (i+2) m₁'',
  { rw [← d_apply, eq_sub_of_add_eq hm₁, normed_group_hom.map_sub, ← category_theory.comp_apply,
       d_comp_d, coe_zero, ← neg_inj, pi.zero_apply, zero_sub], },
  have hle : ∥res (M.d (i+1) (i+2) m₁)∥ ≤ K'' * ∥m₁''∥,
  { calc ∥res (M.d (i+1) (i+2) m₁)∥
        ≤ K'' * ∥f (M.d (i+1) (i+2) m₁)∥ : Hf _ _ him _
    ... = K'' * ∥M'.d (i+1) (i+2) m₁''∥ : by rw [hm₂, norm_neg]
    ... ≤ K'' * ∥m₁''∥ : (mul_le_mul_of_nonneg_left
                           (hM'_adm.d_norm_noninc _ _ _ _ m₁'') $ nnreal.coe_nonneg K'') },
  obtain ⟨i', j, hi', rfl, m₀, hm₀⟩ :=
    hM _ ⟨hc.out.trans $ le_mul_of_one_le_left' hk'.out⟩ _ (nat.succ_le_succ hi) (res m₁) ε₁ hε₁,
  rw [← nat.pred_eq_sub_one, i.pred_succ] at hi', subst i',
  replace hm₀ : ∥res m₁ - M.d i (i+1) m₀∥ ≤ K * K'' * ∥N.d i (i+1) (g m')∥ + K*K''*ε₁ + ε₁,
  { calc ∥res m₁ - M.d i (i+1) m₀∥  = ∥res (res m₁) - M.d i (i+1) m₀∥ : by rw res_res
    ... ≤ K * ∥M.d (i+1) (i+2) (res m₁)∥ + ε₁ : hm₀
    ... = K * ∥res (M.d (i+1) (i+2) m₁)∥ + ε₁ : by rw d_res
    ... ≤ K*(K'' * ∥m₁''∥) + ε₁ : add_le_add_right (mul_le_mul_of_nonneg_left hle nnreal.zero_le_coe) _
    ... ≤ K*(K'' * (∥N.d i (i+1) (g m')∥ + ε₁)) + ε₁ :  add_le_add_right (mul_le_mul_of_nonneg_left
                                        (mul_le_mul_of_nonneg_left hnorm_m₁''.le nnreal.zero_le_coe)
                                         nnreal.zero_le_coe) ε₁
    ... = K * K'' * ∥N.d i (i+1) (g m')∥ + K*K''*ε₁ + ε₁ : by ring },

  let mnew₁' := M'.d i (i+1) (res m' - f m₀),
  have hmnew' : mnew₁' = res m₁'' + f (res m₁ - M.d i (i+1) m₀),
  { exact calc mnew₁'
        = M'.d i (i+1) (res m' - f m₀) : rfl
    ... = res (M'.d i (i+1) m') - (f (M.d i (i+1) m₀)) : by rw [normed_group_hom.map_sub, d_res _, d_apply]
    ... = res (M'.d i (i+1) m') - (f (res m₁)) + (f (res m₁) - f (M.d i (i+1) m₀)) : by abel
    ... = res m₁'' + f ((res m₁) - (M.d i (i+1) m₀)) : by
                        { rw [← system_of_complexes.map_sub, ← res_apply,
                              ← normed_group_hom.map_sub, ← sub_eq_of_eq_add' hm₁.symm] } },
  have hnormle : ∥mnew₁'∥ ≤ (K*K'' + 1)*∥N.d i (i+1) (g m')∥ + (K*K'' + 2) * ε₁,
  { calc ∥mnew₁'∥
        = ∥res m₁'' + f (res m₁ - M.d i (i+1) m₀)∥ : by rw [hmnew']
    ... ≤ ∥res m₁''∥ + ∥f (res m₁ - M.d i (i+1) m₀)∥ : norm_add_le _ _
    ... ≤ ∥m₁''∥ + ∥f (res m₁ - M.d i (i+1) m₀)∥ : add_le_add_right
                                      (hM'_adm.res_norm_noninc _ _ _ infer_instance m₁'') _
    ... ≤ ∥m₁''∥ + ∥res m₁ - M.d i (i+1) m₀∥ : add_le_add_left (hf _ _ _) _
    ... ≤ ∥N.d i (i+1) (g m')∥ + ε₁ + ∥res m₁ - M.d i (i+1) m₀∥ : add_le_add_right (le_of_lt hnorm_m₁'')  _
    ... ≤ ∥N.d i (i+1) (g m')∥ + ε₁ + (K * K'' * ∥N.d i (i+1) (g m')∥ + K * K'' * ε₁ + ε₁) : add_le_add_left hm₀ _
    ... = (K*K'' + 1)*∥d _ _ (i+1) (g m')∥ + (K*K'' + 2) * ε₁ : by ring },
  obtain ⟨i₀, _, hi₀, rfl, mnew₀, hmnew₀⟩ := hM' _ hc _ (hi.trans m.le_succ) (res m' - f m₀) _ hε₁,
  replace hmnew₀ : ∥res (res m' - f m₀) - d _ _ _ mnew₀∥ ≤ K' * ((K * K'' + 1) * ∥N.d i (i+1) (g m')∥ + (K * K'' + 2) * ε₁) + ε₁ :=
    hmnew₀.trans (add_le_add_right (mul_le_mul_of_nonneg_left hnormle nnreal.zero_le_coe) ε₁),
  let nnew₀ : ↥(N c i₀) := g mnew₀,
  have hmnewlift : g (res (res m' - f m₀) - M'.d i₀ i mnew₀) = res (g m') - N.d i₀ i nnew₀,
  { suffices h : g (res m' - f m₀) = res (g m'),
    { rw [system_of_complexes.map_sub, ← res_apply, ← d_apply, h, res_res] },
    rw system_of_complexes.map_sub,
    have hker : f m₀ ∈ g.apply.ker,
    { rw [hg _ _, mem_range _ _],
      exact ⟨m₀, rfl⟩ },
    replace hker : g (f m₀) = 0, { rwa mem_ker at hker },
    rw [hker, sub_zero, ← res_apply] },
  refine ⟨i₀, hi₀, nnew₀, _⟩,
  rw ← hmnewlift,
  refine ((hgquot _ _).norm_le _).trans (hmnew₀.trans (le_of_eq _)),
  have hε₁_ε : (K' * (K * K'' + 2) + 1 : ℝ)*ε₁ = ε := mul_div_cancel' _
    (by { refine (lt_of_lt_of_le zero_lt_one _).ne',
          exact (nnreal.one_le_add'.out : 1 ≤ K' * (K * K'' + 2) + 1) }),
  rw ← hε₁_ε,
  ring,
end

#exit
import system_of_complexes.basic

universe variables u

noncomputable theory
open_locale nnreal
open category_theory opposite normed_group_hom system_of_complexes


variables (M N P : system_of_complexes.{u}) (f : M ⟶ N) (g : N ⟶ P)

/-  I (DT) extracted this lemma to speed up the proof of `weak_normed_snake_dual`. -/
lemma ε₁_pos (a : ℝ≥0) {ε ε₁ : ℝ} (hε : 0 < ε) (hmulε : ε₁ * (1 + a) = ε / 2) :
  0 < ε₁ :=
have one_add_pos : (0 : ℝ) < 1 + a := add_pos_of_pos_of_nonneg zero_lt_one (zero_le a),
calc 0 < ε / 2 / (1 + ↑a) : div_pos (half_pos hε) one_add_pos
   ... = _                : ((eq_div_iff one_add_pos.ne').mpr hmulε).symm

set_option profiler true
/-  I (DT) extracted this lemma to speed up the proof of `weak_normed_snake_dual`. -/
/-  Breaking off the into two terms. -/
lemma norm_sub_le_split {k' c c₁ : ℝ≥0} {i i' i'' : ℕ}
  [hk' : fact (1 ≤ k')]
  [fc : fact (c ≤ c₁)]
  (hfnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (M c i)), ∥(f.apply) x∥ = ∥x∥)
  {n₁ : N (k' * c) i'}
  {n₂ : N c i''}
  {nnew₁ : N c i'}
  {m₁ : M c i'}
  {m : (M c₁ i)}
  (hm₁ : f m₁ = res n₁ - ((N.d i'' i') n₂) - nnew₁) :
  ∥res m - (M.d i' i) m₁∥ ≤
    ∥(res (f m) : N c i) - N.d i' i (res n₁)∥ + ∥(N.d i' i ((N.d i'' i') n₂ + nnew₁) : N c i)∥ :=
calc
∥res m - (M.d i' i) m₁∥ = ∥f (res m - (M.d i' i) m₁)∥ : (hfnorm _ _ _).symm
... = ∥res (f m) - (N.d i' i (res n₁) - N.d i' i ((N.d i'' i') n₂ + nnew₁))∥ :
    by rw [hom_apply, normed_group_hom.map_sub, ←hom_apply, ←hom_apply, ←res_apply,
      ←d_apply, hm₁, sub_sub, normed_group_hom.map_sub]
  ... = ∥(res (f m) - N.d i' i (res n₁)) + N.d i' i ((N.d i'' i') n₂ + nnew₁)∥ :
    by rw [sub_eq_add_neg, neg_sub, sub_eq_neg_add, ← add_assoc, ← sub_eq_add_neg]
  ... ≤ ∥res (f m) - N.d i' i (res n₁)∥ + ∥N.d i' i ((N.d i'' i') n₂ + nnew₁)∥ : norm_add_le _ _





/- The proof of this lemma is deceptively simple, since there is a lot of typeclass work happening
in the background.  In particular, the `c` in the sea of underscores of the second line is crucial.

The hypothesis `(hN_adm : N.admissible)` is only used via `(hN_adm.res_norm_noninc _ c _ _ _)`,
producing the inequality
`(dis : ∥(res (res (f m) - (N.d i' i) n₁) : N c i)∥ ≤ ∥res (f m) - (N.d i' i) n₁∥)`. -/
lemma norm_sub_le_mul_norm_add_lhs {k' K c c₁ : ℝ≥0} {ε₁ : ℝ} {i i' : ℕ}
  [hk' : fact (1 ≤ k')] [fc₁ : fact (k' * c ≤ c₁)] [fc : fact (c ≤ c₁)]
  {n₁ : N (k' * c) i'}
  {m : (M c₁ i)}
  (hN_adm : N.admissible)
  (hn₁ : ∥res (f m) - (N.d i' i) n₁∥ ≤ K * ∥(N.d i (i + 1)) (f m)∥ + ε₁) :
  ∥(res (f m) : N c i) - N.d i' i (res n₁)∥ ≤ K * ∥(N.d i (i + 1)) (f m)∥ + ε₁ :=
calc
    _ = ∥res (res (f m) - (N.d i' i) n₁)∥      : by rw [normed_group_hom.map_sub, d_res, ← res_res]
  ... ≤ K * ∥(N.d i (i + 1)) (f m)∥ + ε₁ : trans (hN_adm.res_norm_noninc _ c _ _ _) hn₁

/- This chain of inequalities converts one of the two summands appearing in the (weak) normed snake
dual lemma. -/
lemma norm_sub_le_mul_norm_add_rhs {k' K K' r₁ r₂ c c₁ : ℝ≥0} {ε₁ ε₂ : ℝ}
  {i i' i'' : ℕ} (hii' : i' + 1 = i)
  [hk' : fact (1 ≤ k')]
  [fc₁ : fact (k' * c ≤ c₁)]
  (hgnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (N c i)), ∥g x∥ ≤ ↑r₁ * ∥x∥)
  {n₁ : N (k' * c) i'}
  {n₂ : N c i''}
  {nnew₁ : N c i'}
  (hN_adm : N.admissible) /- could use (dis : ∥(N.d i' i) nnew₁∥ ≤ ∥nnew₁∥)
                           `hN_adm.d_norm_noninc _ _ i' i nnew₁` -/
  {m : (M c₁ i)}
  (hn₁ : ∥res (f m) - (N.d i' i) n₁∥ ≤ K * ∥(N.d i (i + 1)) (f m)∥ + ε₁)
  (hp₂ : ∥res (g n₁) - (P.d i'' i') (g n₂)∥ ≤ K' * ∥(P.d i' (i' + 1)) (g n₁)∥ + ε₂)
  (hnormnnew₁ : ∥nnew₁∥ ≤ r₂ * ∥g (res n₁ - ((N.d i'' i') n₂))∥)
  (hfm : ∥g ((N.d i' i) n₁)∥ = ∥g (res (f m) - (N.d i' i) n₁)∥) :
  ∥(N.d i' i ((N.d i'' i') n₂ + nnew₁) : N c i)∥ ≤
    K * K' * r₁ * r₂ * ∥(N.d i (i+1)) (f m)∥ + K' * r₁ * r₂ * ε₁ + r₂ * ε₂ :=
calc ∥(N.d i' i ((N.d i'' i') n₂ + nnew₁) : N c i)∥ =
  ∥N.d i' i ((N.d i'' i') n₂ + nnew₁)∥ : rfl
  ... = ∥N.d i' i nnew₁∥ : by simp only [map_add, zero_add, d_d]
  ... ≤ r₂ * ∥g (res n₁ - (N.d i'' i') n₂)∥ : trans (hN_adm.d_norm_noninc _ _ i' i nnew₁) hnormnnew₁
  ... = r₂ * ∥res (g n₁) - P.d i'' i' (g n₂)∥ :
    by rw [hom_apply g, normed_group_hom.map_sub, ←hom_apply, ←hom_apply, ←res_apply _ _ g, ←d_apply]
  ... ≤ r₂ * (K' * ∥P.d i' (i'+1) (g n₁)∥ + ε₂) : mul_le_mul_of_nonneg_left hp₂ r₂.coe_nonneg
  ... = r₂ * (K' * ∥g (res (f m) - N.d i' i n₁)∥ + ε₂) : by rw [d_apply _ _ g _, hii', hfm]
  ... ≤ r₂ * (K' * (r₁ * ∥res (f m) - N.d i' i n₁∥) + ε₂) :
    mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left
      (hgnorm _ _ _) K'.coe_nonneg) _) $ r₂.coe_nonneg
  ... = r₂ * (K' * r₁ * ∥res (f m) - N.d i' i n₁∥ + ε₂) : by rw mul_assoc
  ... ≤ r₂ * (K' * r₁ * (K * ∥(N.d i (i+1)) (f m)∥ + ε₁) + ε₂) :
    mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left
      hn₁ $ mul_nonneg K'.coe_nonneg r₁.coe_nonneg) _) r₂.coe_nonneg
  ... = _ : by ring

lemma norm_sub_le_mul_norm_add {k' K K' r₁ r₂ c c₁ : ℝ≥0} {ε ε₁ ε₂ : ℝ}
  {i i' i'' : ℕ} (hii' : i' + 1 = i)
  [hk' : fact (1 ≤ k')]
  [fc₁ : fact (k' * c ≤ c₁)]
  [fc : fact (c ≤ c₁)]
  (hN_adm : N.admissible)
  (hgnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (N c i)), ∥g x∥ ≤ ↑r₁ * ∥x∥)
  (hfnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (M c i)), ∥(f.apply) x∥ = ∥x∥)
  {n₁ : N (k' * c) i'}
  {n₂ : N c i''}
  {nnew₁ : N c i'}
  {m₁ : M c i'}
  {m : (M c₁ i)}
  (hmulε₁ : ε₁ * (1 + K' * r₁ * r₂) = ε / 2)
  (hle : (r₂ : ℝ) * ε₂ ≤ ε / 2)
  (hn₁ : ∥res (f m) - (N.d i' i) n₁∥ ≤ K * ∥(N.d i (i + 1)) (f m)∥ + ε₁)
  (hp₂ : ∥res (g n₁) - (P.d i'' i') (g n₂)∥ ≤ K' * ∥(P.d i' (i' + 1)) (g n₁)∥ + ε₂)
  (hnormnnew₁ : ∥nnew₁∥ ≤ r₂ * ∥g (res n₁ - ((N.d i'' i') n₂))∥)
  (hm₁ : f m₁ = res n₁ - ((N.d i'' i') n₂) - nnew₁)
  (hfm : ∥g ((N.d i' i) n₁)∥ = ∥g (res (f m) - (N.d i' i) n₁)∥) :
  ∥res m - (M.d i' i) m₁∥ ≤ (K + r₁ * r₂ * K * K') * ∥(M.d i (i + 1)) m∥ + ε :=
calc
∥res m - (M.d i' i) m₁∥ ≤ ∥res (f m) - N.d i' i (res n₁)∥ + ∥N.d i' i ((N.d i'' i') n₂ + nnew₁)∥ :
    norm_sub_le_split M N f hfnorm hm₁
  ... ≤ (K * ∥(N.d i (i + 1)) (f m)∥ + ε₁) +
        (K * K' * r₁ * r₂ * ∥(N.d i (i+1)) (f m)∥ + K' * r₁ * r₂ * ε₁ + r₂ * ε₂) : add_le_add
      (norm_sub_le_mul_norm_add_lhs M N f hN_adm hn₁)
      (norm_sub_le_mul_norm_add_rhs M N P f g hii' hgnorm hN_adm hn₁ hp₂ hnormnnew₁ hfm)
  ... = (K + r₁ * r₂ * K * K') * ∥N.d i (i+1) (f m)∥ + ε₁ * (1 + K' * r₁ * r₂) + r₂ * ε₂ : by ring
  ... = (K + r₁ * r₂ * K * K') * ∥N.d i (i+1) (f m)∥ + ε / 2 + r₂ * ε₂ :
    congr_arg (λ e, (↑K + ↑r₁ * ↑r₂ * ↑K * ↑K') * ∥(N.d i (i + 1)) (f m)∥ + e + ↑r₂ * ε₂) hmulε₁
  ... ≤ (K + r₁ * r₂ * K * K') * ∥N.d i (i+1) (f m)∥ + ε / 2 + ε / 2 : add_le_add_left hle _
  ... = (K + r₁ * r₂ * K * K') * ∥(M.d i (i+1)) m∥ + ε :
    by rw [add_assoc, add_halves', d_apply, hom_apply, hfnorm]



/-
    _ = ∥res (res (f m) - (N.d i' i) n₁)∥      : by rw [normed_group_hom.map_sub, d_res, ← res_res]
  ... ≤ K * ∥(N.d i (i + 1)) (f m)∥ + ε₁ : trans (hN_adm.res_norm_noninc _ c _ _ _) hn₁
-/







/- The RHS -- no ring -/
lemma norm_sub_le_mul_norm_add_rhs_no_ring {k' K K' r₁ r₂ c c₁ : ℝ≥0} {ε₁ ε₂ : ℝ}
  {i i' i'' : ℕ} (hii' : i' + 1 = i)
  [hk' : fact (1 ≤ k')]
  [fc₁ : fact (k' * c ≤ c₁)]
  (hN_adm : N.admissible)
  (hgnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (N c i)), ∥g x∥ ≤ ↑r₁ * ∥x∥)
  {n₁ : N (k' * c) i'}
  {n₂ : N c i''}
  {nnew₁ : N c i'}
  {m : (M c₁ i)}
  (hn₁ : ∥res (f m) - (N.d i' i) n₁∥ ≤ K * ∥(N.d i (i + 1)) (f m)∥ + ε₁)
  (hp₂ : ∥res (g n₁) - (P.d i'' i') (g n₂)∥ ≤ K' * ∥(P.d i' (i' + 1)) (g n₁)∥ + ε₂)
  (hnormnnew₁ : ∥nnew₁∥ ≤ r₂ * ∥g (res n₁ - ((N.d i'' i') n₂))∥)
  (hfm : ∥g ((N.d i' i) n₁)∥ = ∥g (res (f m) - (N.d i' i) n₁)∥)
   :
  ∥(N.d i' i ((N.d i'' i') n₂ + nnew₁) : N c i)∥ ≤
    r₂ * (K' * r₁ * (K * ∥(N.d i (i+1)) (f m)∥ + ε₁) + ε₂) :=
calc ∥(N.d i' i ((N.d i'' i') n₂ + nnew₁) : N c i)∥ =
  ∥N.d i' i ((N.d i'' i') n₂ + nnew₁)∥ : rfl
  ... = ∥N.d i' i nnew₁∥ : by simp only [map_add, zero_add, d_d]
  ... ≤ r₂ * ∥g (res n₁ - (N.d i'' i') n₂)∥ : trans (hN_adm.d_norm_noninc _ _ i' i nnew₁) hnormnnew₁
  ... = r₂ * ∥res (g n₁) - P.d i'' i' (g n₂)∥ :
    by rw [hom_apply g, normed_group_hom.map_sub, ←hom_apply, ←hom_apply, ←res_apply _ _ g, ←d_apply]
  ... ≤ r₂ * (K' * ∥P.d i' (i'+1) (g n₁)∥ + ε₂) : mul_le_mul_of_nonneg_left hp₂ r₂.coe_nonneg
  ... = r₂ * (K' * ∥g (res (f m) - N.d i' i n₁)∥ + ε₂) : by rw [d_apply _ _ g _, hii', hfm]
  ... ≤ r₂ * (K' * (r₁ * ∥res (f m) - N.d i' i n₁∥) + ε₂) :
    mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left
      (hgnorm _ _ _) K'.coe_nonneg) _) $ r₂.coe_nonneg
  ... = r₂ * (K' * r₁ * ∥res (f m) - N.d i' i n₁∥ + ε₂) : by rw mul_assoc
  ... ≤ r₂ * (K' * r₁ * (K * ∥(N.d i (i+1)) (f m)∥ + ε₁) + ε₂) :
    mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left
      hn₁ $ mul_nonneg K'.coe_nonneg r₁.coe_nonneg) _) r₂.coe_nonneg

#lint
#exit


#lint

/-
The RHS
lemma norm_sub_le_mul_norm_add {k' K K' r₁ r₂ c c₁ : ℝ≥0} {ε ε₁ ε₂ : ℝ}
  {i i' i'' : ℕ} (hii' : i' + 1 = i)
  [hk' : fact (1 ≤ k')]
  [fc₁ : fact (k' * c ≤ c₁)]
  [fc : fact (c ≤ c₁)]
  (hN_adm : N.admissible)
  (hgnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (N c i)), ∥g x∥ ≤ ↑r₁ * ∥x∥)
  (hfnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (M c i)), ∥(f.apply) x∥ = ∥x∥)
  {n₁ : N (k' * c) i'}
  {n₂ : N c i''}
  {nnew₁ : N c i'}
  {m₁ : M c i'}
  {m : (M c₁ i)}
  (hmulε₁ : ε₁ * (1 + K' * r₁ * r₂) = ε / 2)
  (hle : (r₂ : ℝ) * ε₂ ≤ ε / 2)
  (hn₁ : ∥res (f m) - (N.d i' i) n₁∥ ≤ K * ∥(N.d i (i + 1)) (f m)∥ + ε₁)
  (hp₂ : ∥res (g n₁) - (P.d i'' i') (g n₂)∥ ≤ K' * ∥(P.d i' (i' + 1)) (g n₁)∥ + ε₂)
  (hnormnnew₁ : ∥nnew₁∥ ≤ r₂ * ∥g (res n₁ - ((N.d i'' i') n₂))∥)
  (hm₁ : f m₁ = res n₁ - ((N.d i'' i') n₂) - nnew₁)
  (hfm : ∥g ((N.d i' i) n₁)∥ = ∥g (res (f m) - (N.d i' i) n₁)∥) :
  ∥res m - (M.d i' i) m₁∥ ≤ (K + r₁ * r₂ * K * K') * ∥(M.d i (i + 1)) m∥ + ε :=
calc
  ... ≤ ∥res (f m) - N.d i' i (res n₁)∥ + ∥N.d i' i ((N.d i'' i') n₂ + nnew₁)∥ : norm_add_le _ _
  ... = ∥res (f m) - N.d i' i (res n₁)∥ + ∥N.d i' i nnew₁∥ : sorry
  ... ≤ ∥res (f m) - N.d i' i (res n₁)∥ + r₂ * ∥g (res n₁ - (N.d i'' i') n₂)∥ : sorry
  ... = ∥res (f m) - N.d i' i (res n₁)∥ + r₂ * ∥res (g n₁) - P.d i'' i' (g n₂)∥ : sorry
  ... ≤ ∥res (f m) - N.d i' i (res n₁)∥ + r₂ * (K' * ∥P.d i' (i'+1) (g n₁)∥ + ε₂) : sorry
  ... = ∥res (res (f m) - (N.d i' i) n₁)∥ + r₂ * (K' * ∥P.d i' (i'+1) (g n₁)∥ + ε₂) : sorry
  ... ≤ K * ∥(N.d i (i + 1)) (f m)∥ + ε₁ + r₂ * (K' * ∥P.d i' (i'+1) (g n₁)∥ + ε₂) : sorry
  ... = K * ∥(N.d i (i + 1)) (f m)∥ + ε₁ + r₂ * (K' * ∥g (res (f m) - N.d i' i n₁)∥ + ε₂) : sorry
  ... ≤ K * ∥(N.d i (i + 1)) (f m)∥ + ε₁ + r₂ * (K' * (r₁ * ∥res (f m) - N.d i' i n₁∥) + ε₂) : sorry
  ... = K * ∥(N.d i (i + 1)) (f m)∥ + ε₁ + r₂ * (K' * r₁ * ∥res (f m) - N.d i' i n₁∥ + ε₂) : sorry
  ... ≤ K * ∥(N.d i (i + 1)) (f m)∥ + ε₁ + r₂ * (K' * r₁ * (K * ∥(N.d i (i+1)) (f m)∥ + ε₁) + ε₂) : sorry
-/
/-  I (DT) extracted this lemma to speed up the proof of `weak_normed_snake_dual`. -/
lemma norm_sub_le_mul_norm_add {k' K K' r₁ r₂ c c₁ : ℝ≥0} {ε ε₁ ε₂ : ℝ}
  {i i' i'' : ℕ} (hii' : i' + 1 = i)
  [hk' : fact (1 ≤ k')]
  [fc₁ : fact (k' * c ≤ c₁)]
  [fc : fact (c ≤ c₁)]
  (hN_adm : N.admissible)
  (hgnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (N c i)), ∥g x∥ ≤ ↑r₁ * ∥x∥)
  (hfnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (M c i)), ∥(f.apply) x∥ = ∥x∥)
  {n₁ : N (k' * c) i'}
  {n₂ : N c i''}
  {nnew₁ : N c i'}
  {m₁ : M c i'}
  {m : (M c₁ i)}
  (hmulε₁ : ε₁ * (1 + K' * r₁ * r₂) = ε / 2)
  (hle : (r₂ : ℝ) * ε₂ ≤ ε / 2)
  (hn₁ : ∥res (f m) - (N.d i' i) n₁∥ ≤ K * ∥(N.d i (i + 1)) (f m)∥ + ε₁)
  (hp₂ : ∥res (g n₁) - (P.d i'' i') (g n₂)∥ ≤ K' * ∥(P.d i' (i' + 1)) (g n₁)∥ + ε₂)
  (hnormnnew₁ : ∥nnew₁∥ ≤ r₂ * ∥g (res n₁ - ((N.d i'' i') n₂))∥)
  (hm₁ : f m₁ = res n₁ - ((N.d i'' i') n₂) - nnew₁)
  (hfm : ∥g ((N.d i' i) n₁)∥ = ∥g (res (f m) - (N.d i' i) n₁)∥) :
  ∥res m - (M.d i' i) m₁∥ ≤ (K + r₁ * r₂ * K * K') * ∥(M.d i (i + 1)) m∥ + ε :=
calc
∥res m - (M.d i' i) m₁∥ = ∥f (res m - (M.d i' i) m₁)∥ : (hfnorm _ _ _).symm
... = ∥res (f m) - (N.d i' i (res n₁) - N.d i' i ((N.d i'' i') n₂ + nnew₁))∥ :
    by rw [hom_apply, normed_group_hom.map_sub, ←hom_apply, ←hom_apply, ←res_apply,
      ←d_apply, hm₁, sub_sub, normed_group_hom.map_sub]
  ... = ∥(res (f m) - N.d i' i (res n₁)) + N.d i' i ((N.d i'' i') n₂ + nnew₁)∥ :
    by rw [sub_eq_add_neg, neg_sub, sub_eq_neg_add, ← add_assoc, ← sub_eq_add_neg]
  ... ≤ ∥res (f m) - N.d i' i (res n₁)∥ + ∥N.d i' i ((N.d i'' i') n₂ + nnew₁)∥ : norm_add_le _ _
  ... = ∥res (f m) - N.d i' i (res n₁)∥ + ∥N.d i' i nnew₁∥ : by simp only [map_add, zero_add, d_d]
  ... ≤ ∥res (f m) - N.d i' i (res n₁)∥ + r₂ * ∥g (res n₁ - (N.d i'' i') n₂)∥ :
    add_le_add_left (le_trans (hN_adm.d_norm_noninc _ _ i' i nnew₁) hnormnnew₁) _
  ... = ∥res (f m) - N.d i' i (res n₁)∥ + r₂ * ∥res (g n₁) - P.d i'' i' (g n₂)∥ :
    by rw [hom_apply g, normed_group_hom.map_sub, ←hom_apply, ←hom_apply, ←res_apply _ _ g,
      ←d_apply]
  ... ≤ ∥res (f m) - N.d i' i (res n₁)∥ + r₂ * (K' * ∥P.d i' (i'+1) (g n₁)∥ + ε₂) :
    add_le_add_left (mul_le_mul_of_nonneg_left hp₂ r₂.coe_nonneg) _
  ... = ∥res (res (f m) - (N.d i' i) n₁)∥ + r₂ * (K' * ∥P.d i' (i'+1) (g n₁)∥ + ε₂) :
    by rw [←res_res, d_res, normed_group_hom.map_sub]
  ... ≤ K * ∥(N.d i (i + 1)) (f m)∥ + ε₁ + r₂ * (K' * ∥P.d i' (i'+1) (g n₁)∥ + ε₂) :
    add_le_add_right (le_trans (hN_adm.res_norm_noninc _ _ _ _ _) hn₁) _
  ... = K * ∥(N.d i (i + 1)) (f m)∥ + ε₁ + r₂ * (K' * ∥g (res (f m) - N.d i' i n₁)∥ + ε₂) :
    by rw [d_apply _ _ g _, hii', hfm]
  ... ≤ K * ∥(N.d i (i + 1)) (f m)∥ + ε₁ + r₂ * (K' * (r₁ * ∥res (f m) - N.d i' i n₁∥) + ε₂) :
    add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left
      (hgnorm _ _ _) K'.coe_nonneg) _) $ r₂.coe_nonneg) _
  ... = K * ∥(N.d i (i + 1)) (f m)∥ + ε₁ + r₂ * (K' * r₁ * ∥res (f m) - N.d i' i n₁∥ + ε₂) :
    by rw mul_assoc
  ... ≤ K * ∥(N.d i (i + 1)) (f m)∥ + ε₁ + r₂ * (K' * r₁ * (K * ∥(N.d i (i+1)) (f m)∥ + ε₁) + ε₂) :
    add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left
      hn₁ $ mul_nonneg K'.coe_nonneg r₁.coe_nonneg) _) r₂.coe_nonneg) _
  ... = (K + r₁ * r₂ * K * K') * ∥N.d i (i+1) (f m)∥ + ε₁ * (1 + K' * r₁ * r₂) + r₂ * ε₂ : by ring
  ... = (K + r₁ * r₂ * K * K') * ∥N.d i (i+1) (f m)∥ + ε / 2 + r₂ * ε₂ :
    congr_arg (λ e, (↑K + ↑r₁ * ↑r₂ * ↑K * ↑K') * ∥(N.d i (i + 1)) (f m)∥ + e + ↑r₂ * ε₂) hmulε₁
  ... ≤ (K + r₁ * r₂ * K * K') * ∥N.d i (i+1) (f m)∥ + ε / 2 + ε / 2 : add_le_add_left hle _
  ... = (K + r₁ * r₂ * K * K') * ∥(M.d i (i+1)) m∥ + ε :
    by rw [add_assoc, add_halves', d_apply, hom_apply, hfnorm]


#exit

/- All terms explicit. -/
calc
∥res m - (M.d i' i) m₁∥
    = ∥f (res m - (M.d i' i) m₁)∥ : sorry
... = ∥res (f m) - (N.d i' i (res n₁) - N.d i' i ((N.d i'' i') n₂ + nnew₁))∥ : sorry
  ... = ∥(res (f m) - N.d i' i (res n₁)) + N.d i' i ((N.d i'' i') n₂ + nnew₁)∥ : sorry
  ... ≤ ∥res (f m) - N.d i' i (res n₁)∥ + ∥N.d i' i ((N.d i'' i') n₂ + nnew₁)∥ : norm_add_le _ _
  ... = ∥res (f m) - N.d i' i (res n₁)∥ + ∥N.d i' i nnew₁∥ : sorry
  ... ≤ ∥res (f m) - N.d i' i (res n₁)∥ + r₂ * ∥g (res n₁ - (N.d i'' i') n₂)∥ : sorry
  ... = ∥res (f m) - N.d i' i (res n₁)∥ + r₂ * ∥res (g n₁) - P.d i'' i' (g n₂)∥ : sorry
  ... ≤ ∥res (f m) - N.d i' i (res n₁)∥ + r₂ * (K' * ∥P.d i' (i'+1) (g n₁)∥ + ε₂) : sorry
  ... = ∥res (res (f m) - (N.d i' i) n₁)∥ + r₂ * (K' * ∥P.d i' (i'+1) (g n₁)∥ + ε₂) : sorry
  ... ≤ K * ∥(N.d i (i + 1)) (f m)∥ + ε₁ + r₂ * (K' * ∥P.d i' (i'+1) (g n₁)∥ + ε₂) : sorry
  ... = K * ∥(N.d i (i + 1)) (f m)∥ + ε₁ + r₂ * (K' * ∥g (res (f m) - N.d i' i n₁)∥ + ε₂) : sorry
  ... ≤ K * ∥(N.d i (i + 1)) (f m)∥ + ε₁ + r₂ * (K' * (r₁ * ∥res (f m) - N.d i' i n₁∥) + ε₂) : sorry
  ... = K * ∥(N.d i (i + 1)) (f m)∥ + ε₁ + r₂ * (K' * r₁ * ∥res (f m) - N.d i' i n₁∥ + ε₂) : sorry
  ... ≤ K * ∥(N.d i (i + 1)) (f m)∥ + ε₁ + r₂ * (K' * r₁ * (K * ∥(N.d i (i+1)) (f m)∥ + ε₁) + ε₂) : sorry
  ... = (K + r₁ * r₂ * K * K') * ∥N.d i (i+1) (f m)∥ + ε₁ * (1 + K' * r₁ * r₂) + r₂ * ε₂ : sorry
  ... = (K + r₁ * r₂ * K * K') * ∥N.d i (i+1) (f m)∥ + ε / 2 + r₂ * ε₂ : sorry
  ... ≤ (K + r₁ * r₂ * K * K') * ∥N.d i (i+1) (f m)∥ + ε / 2 + ε / 2 : sorry
  ... = (K + r₁ * r₂ * K * K') * ∥(M.d i (i+1)) m∥ + ε : sorry



calc ∥res m - (M.d i' i) m₁∥ = ∥f (res m - (M.d i' i) m₁)∥ : (hfnorm _ _ _).symm
  ... = ∥res _ - (N.d i' i (res n₁) - N.d i' i (_ + nnew₁))∥ :
    by rw [hom_apply, normed_group_hom.map_sub, ←hom_apply, ←hom_apply, ←res_apply,
      ←d_apply, hm₁, sub_sub, normed_group_hom.map_sub]
  ... = ∥(res _ - N.d i' i (res n₁)) + N.d i' i (_ + nnew₁)∥ : by abel
  ... ≤ ∥res _ - N.d i' i _∥ + ∥N.d i' i (_ + nnew₁)∥ : norm_add_le _ _
  ... = ∥res _ - N.d i' i _∥ + ∥N.d i' i nnew₁∥ : by simp only [map_add, zero_add, d_d]
  ... ≤ ∥res _ - N.d i' i _∥ + r₂ * ∥g (res n₁ - _)∥ :
    add_le_add_left (le_trans (hN_adm.d_norm_noninc _ _ i' i nnew₁) hnormnnew₁) _
  ... = ∥res _ - N.d i' i _∥ + r₂ * ∥res _ - P.d i'' i' (g n₂)∥ :
    by rw [hom_apply g, normed_group_hom.map_sub, ←hom_apply, ←hom_apply, ←res_apply _ _ g,
      ←d_apply]
  ... ≤ ∥res _ - N.d i' i _∥ + r₂ * (K' * ∥P.d i' (i'+1) _∥ + ε₂) :
    add_le_add_left (mul_le_mul_of_nonneg_left hp₂ r₂.coe_nonneg) _
  ... = _ + r₂ * (K' * ∥P.d i' (i'+1) _∥ + ε₂) :
    by rw [←res_res, d_res, normed_group_hom.map_sub]
  ... ≤ K * _ + ε₁ + r₂ * (K' * ∥P.d i' (i'+1) _∥ + ε₂) :
    add_le_add_right (le_trans (hN_adm.res_norm_noninc _ _ _ _ _) hn₁) _
  ... = K * _ + ε₁ + r₂ * (K' * ∥g (res (f m) - N.d i' i n₁)∥ + ε₂) :
    by rw [d_apply _ _ g _, hii', hfm]
  ... ≤ K * _ + ε₁ + r₂ * (K' * (r₁ * ∥res (f m) - N.d i' i n₁∥) + ε₂) :
    add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left
      (hgnorm _ _ _) K'.coe_nonneg) _) $ r₂.coe_nonneg) _
  ... = K * _ + ε₁ + r₂ * (K' * r₁ * ∥res _ - N.d i' i n₁∥ + ε₂) : by rw mul_assoc
  ... ≤ K * _ + ε₁ + r₂ * (K' * r₁ * (K * ∥(N.d i (i+1)) _∥ + ε₁) + ε₂) :
    add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left
      hn₁ $ mul_nonneg K'.coe_nonneg r₁.coe_nonneg) _) r₂.coe_nonneg) _
  ... = (K + r₁ * r₂ * K * K') * ∥N.d i (i+1) (f m)∥ + ε₁ * (1 + K' * r₁ * r₂) + r₂ * ε₂ : by ring
  ... = (K + r₁ * r₂ * K * K') * ∥N.d i (i+1) (f m)∥ + ε / 2 + r₂ * ε₂ :
    congr_arg (λ e, (↑K + ↑r₁ * ↑r₂ * ↑K * ↑K') * ∥(N.d i (i + 1)) (f m)∥ + e + ↑r₂ * ε₂) hmulε₁
  ... ≤ _ * ∥N.d i (i+1) (f m)∥ + ε / 2 + ε / 2 : add_le_add_left hle _
  ... = _ * ∥(M.d i (i+1)) m∥ + ε : by rw [add_assoc, add_halves', d_apply, hom_apply, hfnorm]



import system_of_complexes.basic

universe variables u

noncomputable theory
open_locale nnreal
open category_theory opposite normed_group_hom system_of_complexes


variables (M N P : system_of_complexes.{u}) (f : M ⟶ N) (g : N ⟶ P)

lemma ε₁_le_ε {ε ε₁ : ℝ} (hε : 0 ≤ ε) (mK : ℝ≥0) (hε₁ : ε₁ = ε / 2 * (1 + mK)⁻¹) :
  ε₁ ≤ ε :=
sorry

lemma norm_sub_le_mul_mul_norm_add {M N : system_of_complexes} {f : M ⟶ N}
  {k k' K c : ℝ≥0} (mK : ℝ≥0) {ε ε₁ : ℝ} {m : M (k * (k' * c)) 0} {n₁ : N (k' * c) 0} {m₁ : M c 0}
  (ee1 : ε₁ ≤ ε)
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')]
  (hfnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (M c i)), ∥(f.apply) x∥ = ∥x∥)
  (inadm : ∥((res (res m : (M (k' * c) 0))) : (M c 0))∥ ≤ ∥(res m : (M (k' * c) 0))∥ )
  (hn₁ : ∥res (f m) - (N.d 0 0) n₁∥ ≤ ↑K * ∥(N.d 0 (0 + 1)) (f m)∥ + ε₁) :
  ∥res m - (M.d 0 0) m₁∥ ≤ (K * (1 + mK)) * ∥(M.d 0 (0 + 1)) m∥ + ε :=
sorry

lemma norm_sub_le_mul_norm_add {k' K K' r₁ r₂ c c₁ : ℝ≥0} {ε ε₁ ε₂ : ℝ}
  {i i' i'' : ℕ} (hii' : i' + 1 = i)
  [hk' : fact (1 ≤ k')]
  [fc₁ : fact (k' * c ≤ c₁)]
  [fc : fact (c ≤ c₁)]
  (hN_adm : N.admissible)
  (hgnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (N c i)), ∥g x∥ ≤ ↑r₁ * ∥x∥)
  (hfnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (M c i)), ∥(f.apply) x∥ = ∥x∥)
  {n₁ : N (k' * c) i'}
  {n₂ : N c i''}
  {nnew₁ : N c i'}
  {m₁ : M c i'}
  {m : (M c₁ i)}
  (hmulε₁ : ε₁ * (1 + K' * r₁ * r₂) = ε / 2)
  (hle : (r₂ : ℝ) * ε₂ ≤ ε / 2)
  (hn₁ : ∥res (f m) - (N.d i' i) n₁∥ ≤ K * ∥(N.d i (i + 1)) (f m)∥ + ε₁)
  (hp₂ : ∥res (g n₁) - (P.d i'' i') (g n₂)∥ ≤ K' * ∥(P.d i' (i' + 1)) (g n₁)∥ + ε₂)
  (hnormnnew₁ : ∥nnew₁∥ ≤ r₂ * ∥g (res n₁ - ((N.d i'' i') n₂))∥)
  (hm₁ : f m₁ = res n₁ - ((N.d i'' i') n₂) - nnew₁)
  (hfm : ∥g ((N.d i' i) n₁)∥ = ∥g (res (f m) - (N.d i' i) n₁)∥) :
  ∥res m - (M.d i' i) m₁∥ ≤ (K + r₁ * r₂ * K * K') * ∥(M.d i (i + 1)) m∥ + ε :=
sorry

lemma exists_norm_sub_le_mul_add {M : system_of_complexes} {k k' c ρ : ℝ≥0}
  {i : ℕ}
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')]
  (hM_adm : M.admissible)
  (ex_le : (∀ (m : (M (k * (k' * c)) i)) (ε : ℝ), 0 < ε →
        (∃ (i₀ : ℕ) (hi₀ : i₀ = i - 1) (y : (M c i₀)),
           ∥res m - (M.d i₀ i) y∥ ≤ ↑ρ * ∥(M.d i (i + 1)) m∥ + ε)))
  (m₁ : (M (k * k' * c) i))
  {ε : ℝ}
  (hε : 0 < ε) :
  ∃ (i₀ j : ℕ) (hi₀ : i₀ = i - 1) (hj : i + 1 = j) (y : (M c i₀)),
      ∥res m₁ - (M.d i₀ i) y∥ ≤ ↑ρ * ∥(M.d i j) m₁∥ + ε :=
sorry

lemma exists_norm_sub_le_mul {M : system_of_complexes} {k k' c ρ : ℝ≥0}
  {i : ℕ}
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')]
  (hM_adm : M.admissible)
  (ex_le : (∀ (m : (M (k * (k' * c)) i)),
        (∃ (i₀ : ℕ) (hi₀ : i₀ = i - 1) (y : (M c i₀)),
           ∥res m - (M.d i₀ i) y∥ ≤ ↑ρ * ∥(M.d i (i + 1)) m∥)))
  (m₁ : (M (k * k' * c) i)) :
  ∃ (i₀ j : ℕ) (hi₀ : i₀ = i - 1) (hj : i + 1 = j) (y : (M c i₀)),
      ∥res m₁ - (M.d i₀ i) y∥ ≤ ↑ρ * ∥(M.d i j) m₁∥ :=
sorry

lemma norm_sub_le_mul_mul_norm {M N : system_of_complexes} {f : M ⟶ N}
  {k k' K c : ℝ≥0} (mK : ℝ≥0) {m : M (k * (k' * c)) 0} {n₁ : N (k' * c) 0} {m₁ : M c 0}
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')]
  (hfnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (M c i)), ∥(f.apply) x∥ = ∥x∥)
  (inadm : ∥((res (res m : (M (k' * c) 0))) : (M c 0))∥ ≤ ∥(res m : (M (k' * c) 0))∥ )
  (hn₁ : ∥res (f m) - (N.d 0 0) n₁∥ ≤ ↑K * ∥(N.d 0 (0 + 1)) (f m)∥) :
  ∥res m - (M.d 0 0) m₁∥ ≤ (K * (1 + mK)) * ∥(M.d 0 (0 + 1)) m∥ :=
sorry



/-  Extracted lemma. -/
lemma exist_norm_sub_le_mul_norm_add {M N P : system_of_complexes} {k k' K K' r₁ r₂ c₀ c : ℝ≥0}
  {a i : ℕ}
  (ε : ℝ) -- keep explicit to work with positive, for weak, and with zero, for non-weak
  {f : M ⟶ N} {g : N ⟶ P}
  [hk : fact (1 ≤ k)]
  [hk' : fact (1 ≤ k')]
  (hN_adm : N.admissible)
  (hgnrm : ∀ (c : ℝ≥0) (i : ℕ) (x : (N c i)), ∥g x∥ ≤ r₁ * ∥x∥)
  (Hg : ∀ (c : ℝ≥0) [_inst_1 : fact (c₀ ≤ c)] (i : ℕ),
          i ≤ a + 1 + 1 → ∀ (y : (P c i)), ∃ (x : (N c i)), g x = y ∧ ∥x∥ ≤ r₂ * ∥y∥)
  (hg : ∀ (c : ℝ≥0) (i : ℕ), (range f.apply : add_subgroup (N c i)) = ker g.apply)
  (hf : ∀ (c : ℝ≥0) (i : ℕ), (isometry (f.apply : M c i ⟶ N c i) : _))
  (hc : fact (c₀ ≤ c))
  (hi : i ≤ a)
  (m : (M (k * (k' * c)) i))
  (hε : 0 ≤ ε)
  (n₁ : (N (k' * c) (i - 1)))
  (hn₁ : ∥res (f m) - (N.d (i - 1) i) n₁∥ ≤
    K * ∥(N.d i (i + 1)) (f m)∥ + ε / 2 * (1 + K' * r₁ * r₂)⁻¹)
  (Hi' : i - 1 ≤ a + 1)
  (p₂ : (P c (i - 1 - 1)))
  (hp₂ : ∥res (g n₁) - (P.d (i - 1 - 1) (i - 1)) p₂∥ ≤
    K' * ∥(P.d (i - 1) (i - 1 + 1)) (g n₁)∥ + ite (r₂ = 0) 1 (ε / 2 * (r₂)⁻¹)) :
  ∃ (i₀ : ℕ) (hi₀ : i₀ = i - 1) (y : (M c i₀)),
    ∥res m - (M.d i₀ i) y∥ ≤ (K + r₁ * r₂ * K * K') * ∥(M.d i (i + 1)) m∥ + ε :=
begin
  have hlt : 0 < 1 + K' * r₁ * r₂ := add_pos_of_pos_of_nonneg zero_lt_one (zero_le _),
    have Hi'' : (i - 1 - 1) ≤ a + 1 + 1 := trans (nat.pred_le _) (trans Hi' (nat.le_succ _)),
    obtain ⟨n₂, rfl, hnormn₂⟩ := Hg c (i - 1 - 1) Hi'' p₂,
    let n₁' := N.d (i - 1 - 1) (i - 1) n₂,
    obtain ⟨nnew₁, hnnew₁, hnrmnew₁⟩ := Hg c (i - 1) (trans Hi' a.succ.le_succ) (g (res n₁ - n₁')),
    have hker : (res n₁ - n₁') - nnew₁ ∈ g.apply.ker,
    { rw [mem_ker, normed_group_hom.map_sub, sub_eq_zero, ←hom_apply, ←hom_apply, hnnew₁] },
    rw ←hg at hker,
    obtain ⟨m₁, hm₁ : f m₁ = res n₁ - n₁' - nnew₁⟩ := (mem_range _ _).1 hker,
    refine ⟨i - 1, rfl, m₁, _⟩,

    have hfnrm : ∀ c i (x : M c i), ∥f.apply x∥ = ∥x∥ :=
      λ c i x, (isometry_iff_norm _).1 (hf c i) x,
    by_cases hizero : i = 0,
    { subst hizero,
      convert norm_sub_le_mul_mul_norm_add (K' * r₁ * r₂) _ hfnrm _ hn₁,
      { norm_cast, ring },
      { exact ε₁_le_ε hε (K' * r₁ * r₂) rfl },
      { exact (admissible_of_isometry hN_adm hf).res_norm_noninc _ _ _ _ _ } },

    { refine norm_sub_le_mul_norm_add M N P f g _ hN_adm hgnrm hfnrm _ _ hn₁ hp₂ hnrmnew₁ hm₁ _,
      { exact nat.succ_pred_eq_of_pos (nat.pos_of_ne_zero hizero) },
      { rw inv_mul_cancel_right', exact_mod_cast hlt.ne' },
      { by_cases H : r₂ = 0,
        { simp only [H, nnreal.coe_zero, if_true, zero_mul, (div_nonneg hε zero_le_two)] },
        { simp only [H, nnreal.coe_eq_zero, if_false, mul_comm,
            mul_inv_cancel_left' (nnreal.coe_ne_zero.mpr H)] } },
      { have : f (res m : M (k' * c) i) ∈ f.apply.range, { rw mem_range, exact ⟨res m, rfl⟩ },
        rw [hg, mem_ker] at this,
        rw [hom_apply g (res (f m) - (N.d (i - 1) i) n₁), res_apply, normed_group_hom.map_sub, this,
          zero_sub, norm_neg, ←hom_apply] } }
end

lemma weak_normed_snake_dual (k k' K K' r₁ r₂ : ℝ≥0)
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')]
  {a : ℕ} {c₀ : ℝ≥0}
  (hN : N.is_weak_bounded_exact k K (a + 1) c₀)
  (hP : P.is_weak_bounded_exact k' K' (a + 1) c₀)
  (hN_adm : N.admissible)
  (hgnrm : ∀ c i (x : N c i), ∥g x∥ ≤ r₁ * ∥x∥)
  (Hg : ∀ (c : ℝ≥0) [fact (c₀ ≤ c)] (i : ℕ) (hi : i ≤ a + 1 + 1) (y : P c i),
    ∃ (x : N c i), g x = y ∧ ∥x∥ ≤ r₂ * ∥y∥)
  (hg : ∀ c i, (f.apply : M c i ⟶ N c i).range = g.apply.ker)
  (hf : ∀ c i, @isometry (M c i) (N c i) _ _ f.apply) :
  M.is_weak_bounded_exact (k * k') (K + r₁ * r₂ * K * K') a c₀ :=
begin
  introsI c hc i hi,
  apply exists_norm_sub_le_mul_add (admissible_of_isometry hN_adm hf),
  intros m ε hε,

  have hlt : 0 < (1 + K' * r₁ * r₂ : ℝ) :=
    add_pos_of_pos_of_nonneg zero_lt_one ((K' * r₁ * r₂).coe_nonneg),
  have hε₁ : 0 < ε / 2 * (1 + K' * r₁ * r₂)⁻¹ := mul_pos (half_pos hε) (inv_pos.2 hlt),
  obtain ⟨_, _, rfl, rfl, n₁, hn₁⟩ :=
    hN _ ⟨hc.out.trans $ le_mul_of_one_le_left' hk'.out⟩ _ (trans hi a.le_succ) (f m) _ hε₁,
  have Hi' : i - 1 ≤ a + 1 := trans i.pred_le (trans hi a.le_succ),
  obtain ⟨_, _, rfl, rfl, p₂, hp₂⟩ := hP _ hc _ Hi' (g n₁)
    (if (r₂ : ℝ) = 0 then 1 else (ε / 2) * r₂⁻¹) _,
  { simp_rw [nnreal.coe_eq_zero r₂] at hp₂,
    apply exist_norm_sub_le_mul_norm_add ε hN_adm hgnrm Hg hg hf
      hc hi m hε.le n₁ hn₁ Hi' p₂,
    convert hp₂, },
  { by_cases H : r₂ = 0,
    { simp only [H, zero_lt_one, if_true, eq_self_iff_true, nnreal.coe_eq_zero] },
    { simp only [H, nnreal.coe_eq_zero, if_false],
      exact mul_pos (half_pos hε) (inv_pos.2 (nnreal.coe_pos.2 (zero_lt_iff.2 H))) } }
end

lemma normed_snake_dual {k k' K K' r₁ r₂ : ℝ≥0}
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')]
  {a : ℕ} {c₀ : ℝ≥0}
  (hN : N.is_bounded_exact k K (a + 1) c₀)
  (hP : P.is_bounded_exact k' K' (a + 1) c₀)
  (hN_adm : N.admissible)
  (hgnorm : ∀ c i (x : N c i), ∥g x∥ ≤ r₁ * ∥x∥)
  (Hg : ∀ (c : ℝ≥0) [fact (c₀ ≤ c)] (i : ℕ) (hi : i ≤ a + 1 + 1) (y : P c i),
    ∃ (x : N c i), g x = y ∧ ∥x∥ ≤ r₂ * ∥y∥)
  (hg : ∀ c i, (f.apply : M c i ⟶ N c i).range = g.apply.ker)
  (hf : ∀ c i, @isometry (M c i) (N c i) _ _ f.apply) :
  M.is_bounded_exact (k * k') (K + r₁ * r₂ * K * K') a c₀ :=
begin
  introsI c hc i hi,
  refine exists_norm_sub_le_mul (admissible_of_isometry hN_adm hf) _,

  intro m,

  obtain ⟨_, _, rfl, rfl, n₁, hn₁⟩ :=
    hN _ ⟨hc.out.trans $ le_mul_of_one_le_left' hk'.out⟩ _ (trans hi a.le_succ) (f m),
  have Hi' : (i - 1) ≤ a + 1 := trans i.pred_le (trans hi a.le_succ),
  obtain ⟨_, _, rfl, rfl, p₂, hp₂⟩ := hP _ hc _ Hi' (g n₁),
  rw ← add_zero (_ * ∥_∥) at ⊢,
  have hn₁₁ :  ∥res (f m) - (N.d (i - 1) i) n₁∥ ≤
    K * ∥(N.d i (i + 1)) (f m)∥ + 0 / 2 * (1 + K' * r₁ * r₂)⁻¹, rwa [zero_div, zero_mul, add_zero],
  obtain F := exist_norm_sub_le_mul_norm_add 0 hN_adm
    hgnorm Hg hg hf hc hi m rfl.le n₁ hn₁₁ Hi' p₂,
  by_cases hr : r₂ = 0,
  { subst hr,
    simp at ⊢ F,
    exact F (trans hp₂ (le_add_of_nonneg_right zero_le_one)) },
  { exact F (by { convert hp₂, simp [hr] } ) }
end

#lint
#exit
  have Hi'' : (i - 1 - 1) ≤ a + 1 + 1 := trans (nat.pred_le _) (trans Hi' (nat.le_succ _)),
  obtain ⟨n₂, rfl, hnormn₂⟩ := Hg c (i - 1 - 1) Hi'' p₂,
  let n₁' := N.d (i - 1 - 1) (i - 1) n₂,
  obtain ⟨nnew₁, hnnew₁, hnormnnew₁⟩ := Hg c (i - 1) (trans Hi' (nat.le_succ _)) (g (res n₁ - n₁')),
  have hker : (res n₁ - n₁') - nnew₁ ∈ g.apply.ker,
  { rw [mem_ker, normed_group_hom.map_sub, sub_eq_zero, ←hom_apply, ←hom_apply, hnnew₁] },
  rw ←hg at hker,
  obtain ⟨m₁, hm₁ : f m₁ = res n₁ - n₁' - nnew₁⟩ := (mem_range _ _).1 hker,
  refine ⟨i - 1, rfl, m₁, _⟩,

  have hfnorm : ∀ c i (x : M c i), ∥f.apply x∥ = ∥x∥ := λ c i x, (isometry_iff_norm _).1 (hf c i) x,
  by_cases hizero : i = 0,
  { subst hizero,
    convert norm_sub_le_mul_mul_norm (K' * r₁ * r₂) hfnorm _ hn₁,
    { norm_cast, ring },
    { exact (admissible_of_isometry hN_adm hf).res_norm_noninc _ _ _ _ _ } },

  have hii' : i - 1 + 1 = i,
  { rw [nat.sub_one, nat.add_one, nat.succ_pred_eq_of_pos (zero_lt_iff.mpr hizero)] },
  have hfm : ∥g (N.d (i - 1) i n₁)∥ = ∥g (res (f m) - N.d (i - 1) i n₁)∥,
  { have : f (@res _ _ (k' * c) _ _ m) ∈ f.apply.range := by { rw mem_range, exact ⟨res m, rfl⟩ },
    rw [hg, mem_ker] at this,
    rw [hom_apply g (res (f m) - (N.d _ i) n₁), res_apply, normed_group_hom.map_sub, this,
      zero_sub, norm_neg, ←hom_apply] },
  rw ← add_zero (_ * ∥_∥) at ⊢ hn₁ hp₂,
  apply norm_sub_le_mul_norm_add M N P f g hii' hN_adm hgnorm hfnorm _ _ hn₁ hp₂ hnormnnew₁ hm₁ hfm;
  simp,
end


#lint
#exit
/-  Attempt to reuse lemmas with ε = 0. -/
import system_of_complexes.basic

universe variables u

noncomputable theory
open_locale nnreal
open category_theory opposite normed_group_hom system_of_complexes


variables (M N P : system_of_complexes.{u}) (f : M ⟶ N) (g : N ⟶ P)

/-  I (DT) extracted this lemma to speed up the proof of `weak_normed_snake_dual`. -/
lemma ε₁_pos (a : ℝ≥0) {ε ε₁ : ℝ} (hε : 0 < ε) (hmulε : ε₁ * (1 + a) = ε / 2) :
  0 < ε₁ :=
have one_add_pos : (0 : ℝ) < 1 + a := add_pos_of_pos_of_nonneg zero_lt_one (zero_le a),
calc 0 < ε / 2 / (1 + ↑a) : div_pos (half_pos hε) one_add_pos
   ... = _                : ((eq_div_iff one_add_pos.ne').mpr hmulε).symm

/-  I (DT) extracted this lemma to speed up the proof of `weak_normed_snake_dual`. -/
lemma norm_sub_le_mul_norm_add {k' K K' r₁ r₂ c c₁ : ℝ≥0} {ε ε₁ ε₂ : ℝ}
  {i i' i'' : ℕ} (hii' : i' + 1 = i)
  [hk' : fact (1 ≤ k')]
  [fc₁ : fact (k' * c ≤ c₁)]
  [fc : fact (c ≤ c₁)]
  (hN_adm : N.admissible)
  (hgnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (N c i)), ∥g x∥ ≤ ↑r₁ * ∥x∥)
  (hfnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (M c i)), ∥(f.apply) x∥ = ∥x∥)
  {n₁ : N (k' * c) i'}
  {n₂ : N c i''}
  {nnew₁ : N c i'}
  {m₁ : M c i'}
  {m : (M c₁ i)}
  (hmulε₁ : ε₁ * (1 + K' * r₁ * r₂) = ε / 2)
  (hle : (r₂ : ℝ) * ε₂ ≤ ε / 2)
  (hn₁ : ∥res (f m) - (N.d i' i) n₁∥ ≤ K * ∥(N.d i (i + 1)) (f m)∥ + ε₁)
  (hp₂ : ∥res (g n₁) - (P.d i'' i') (g n₂)∥ ≤ K' * ∥(P.d i' (i' + 1)) (g n₁)∥ + ε₂)
  (hnormnnew₁ : ∥nnew₁∥ ≤ r₂ * ∥g (res n₁ - ((N.d i'' i') n₂))∥)
  (hm₁ : f m₁ = res n₁ - ((N.d i'' i') n₂) - nnew₁)
  (hfm : ∥g ((N.d i' i) n₁)∥ = ∥g (res (f m) - (N.d i' i) n₁)∥) :
  ∥res m - (M.d i' i) m₁∥ ≤ (K + r₁ * r₂ * K * K') * ∥(M.d i (i + 1)) m∥ + ε :=
calc ∥res m - (M.d i' i) m₁∥ = ∥f (res m - (M.d i' i) m₁)∥ : (hfnorm _ _ _).symm
  ... = ∥res _ - (N.d i' i (res n₁) - N.d i' i (_ + nnew₁))∥ :
    by rw [hom_apply, normed_group_hom.map_sub, ←hom_apply, ←hom_apply, ←res_apply,
      ←d_apply, hm₁, sub_sub, normed_group_hom.map_sub]
  ... = ∥(res _ - N.d i' i (res n₁)) + N.d i' i (_ + nnew₁)∥ : by abel
  ... ≤ ∥res _ - N.d i' i _∥ + ∥N.d i' i (_ + nnew₁)∥ : norm_add_le _ _
  ... = ∥res _ - N.d i' i _∥ + ∥N.d i' i nnew₁∥ : by simp only [map_add, zero_add, d_d]
  ... ≤ ∥res _ - N.d i' i _∥ + r₂ * ∥g (res n₁ - _)∥ :
    add_le_add_left (le_trans (hN_adm.d_norm_noninc _ _ i' i nnew₁) hnormnnew₁) _
  ... = ∥res _ - N.d i' i _∥ + r₂ * ∥res _ - P.d i'' i' (g n₂)∥ :
    by rw [hom_apply g, normed_group_hom.map_sub, ←hom_apply, ←hom_apply, ←res_apply _ _ g,
      ←d_apply]
  ... ≤ ∥res _ - N.d i' i _∥ + r₂ * (K' * ∥P.d i' (i'+1) _∥ + ε₂) :
    add_le_add_left (mul_le_mul_of_nonneg_left hp₂ r₂.coe_nonneg) _
  ... = _ + r₂ * (K' * ∥P.d i' (i'+1) _∥ + ε₂) :
    by rw [←res_res, d_res, normed_group_hom.map_sub]
  ... ≤ K * _ + ε₁ + r₂ * (K' * ∥P.d i' (i'+1) _∥ + ε₂) :
    add_le_add_right (le_trans (hN_adm.res_norm_noninc _ _ _ _ _) hn₁) _
  ... = K * _ + ε₁ + r₂ * (K' * ∥g (res (f m) - N.d i' i n₁)∥ + ε₂) :
    by rw [d_apply _ _ g _, hii', hfm]
  ... ≤ K * _ + ε₁ + r₂ * (K' * (r₁ * ∥res (f m) - N.d i' i n₁∥) + ε₂) :
    add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left
      (hgnorm _ _ _) K'.coe_nonneg) _) $ r₂.coe_nonneg) _
  ... = K * _ + ε₁ + r₂ * (K' * r₁ * ∥res _ - N.d i' i n₁∥ + ε₂) : by rw mul_assoc
  ... ≤ K * _ + ε₁ + r₂ * (K' * r₁ * (K * ∥(N.d i (i+1)) _∥ + ε₁) + ε₂) :
    add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left
      hn₁ $ mul_nonneg K'.coe_nonneg r₁.coe_nonneg) _) r₂.coe_nonneg) _
  ... = (K + r₁ * r₂ * K * K') * ∥N.d i (i+1) (f m)∥ + ε₁ * (1 + K' * r₁ * r₂) + r₂ * ε₂ : by ring
  ... = (K + r₁ * r₂ * K * K') * ∥N.d i (i+1) (f m)∥ + ε / 2 + r₂ * ε₂ :
    congr_arg (λ e, (↑K + ↑r₁ * ↑r₂ * ↑K * ↑K') * ∥(N.d i (i + 1)) (f m)∥ + e + ↑r₂ * ε₂) hmulε₁
  ... ≤ _ * ∥N.d i (i+1) (f m)∥ + ε / 2 + ε / 2 : add_le_add_left hle _
  ... = _ * ∥(M.d i (i+1)) m∥ + ε : by rw [add_assoc, add_halves', d_apply, hom_apply, hfnorm]

/-  I (DT) extracted this lemma to speed up the proof of `weak_normed_snake_dual`.
The `ρ` in this lemma stands for `K + r₁ * r₂ * K * K'` in the application. -/
lemma exists_norm_sub_le_mul_add {M : system_of_complexes} {k k' c ρ : ℝ≥0}
  {i : ℕ}
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')]
  (hM_adm : M.admissible)
  (ex_le : (∀ (m : (M (k * (k' * c)) i)) (ε : ℝ), 0 < ε →
        (∃ (i₀ : ℕ) (hi₀ : i₀ = i - 1) (y : (M c i₀)),
           ∥res m - (M.d i₀ i) y∥ ≤ ↑ρ * ∥(M.d i (i + 1)) m∥ + ε)))
  (m₁ : (M (k * k' * c) i))
  {ε : ℝ}
  (hε : 0 < ε) :
  ∃ (i₀ j : ℕ) (hi₀ : i₀ = i - 1) (hj : i + 1 = j) (y : (M c i₀)),
      ∥res m₁ - (M.d i₀ i) y∥ ≤ ↑ρ * ∥(M.d i j) m₁∥ + ε :=
begin
  haveI : fact (k * (k' * c) ≤ k * k' * c) := { out := (mul_assoc _ _ _).symm.le },
  rcases ex_le (res m₁) ε hε with ⟨i₀, rfl, y, hy⟩,
  rw [res_res, d_res] at hy,
  refine ⟨i - 1, _, rfl, rfl, _⟩,
  refine ⟨y, hy.trans (add_le_add_right (mul_le_mul_of_nonneg_left _ ρ.2) ε)⟩,
  exact hM_adm.res_norm_noninc _ _ _ _ _,
end

/-  I (DT) extracted this lemma to speed up the proof of `weak_normed_snake_dual`. -/
lemma norm_sub_le_mul_mul_norm_add {M N : system_of_complexes} {f : M ⟶ N}
  {k k' K c : ℝ≥0} (mK : ℝ≥0) {ε ε₁ : ℝ} {m : M (k * (k' * c)) 0} {n₁ : N (k' * c) 0} {m₁ : M c 0}
  (ee1 : ε₁ ≤ ε)
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')]
  (hfnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (M c i)), ∥(f.apply) x∥ = ∥x∥)
  (inadm : ∥((res (res m : (M (k' * c) 0))) : (M c 0))∥ ≤ ∥(res m : (M (k' * c) 0))∥ )
  (hn₁ : ∥res (f m) - (N.d 0 0) n₁∥ ≤ ↑K * ∥(N.d 0 (0 + 1)) (f m)∥ + ε₁) :
  ∥res m - (M.d 0 0) m₁∥ ≤ (K * (1 + mK)) * ∥(M.d 0 (0 + 1)) m∥ + ε :=
begin
  simp only [d_self_apply, sub_zero, nnreal.coe_add, nnreal.coe_mul] at hn₁ ⊢,
  rw [res_apply, hom_apply f (res m), hfnorm] at hn₁,
  have new : fact (c ≤ k' * c) := { out := le_mul_of_one_le_left c.2 hk'.out },
  rw ←res_res _ _ _ new,
  refine le_trans inadm (le_trans hn₁ _),
  rw [d_apply, hom_apply f _, hfnorm],
  refine add_le_add _ ee1,
  rw mul_assoc,
  refine (mul_le_mul_of_nonneg_left _ K.2),
  exact le_mul_of_one_le_left (norm_nonneg _) (le_add_of_nonneg_right mK.2),
end

/-  I (DT) extracted this lemma to speed up the proof of `weak_normed_snake_dual`. -/
lemma ε₁_le_ε {ε ε₁ : ℝ} (hε : 0 < ε) (mK : ℝ≥0) (hε₁ : ε₁ = ε / 2 * (1 + mK)⁻¹) :
  ε₁ ≤ ε :=
begin
  rw [hε₁, div_eq_mul_inv, mul_assoc, ← mul_inv'],
  refine mul_le_of_le_one_right (le_of_lt hε) _,
  rw mul_inv',
  refine mul_le_one nnreal.two_inv_lt_one.le (inv_nonneg.mpr (add_nonneg zero_le_one _)) _,
  { exact mK.coe_nonneg },
  { exact inv_le_one (le_add_of_nonneg_right mK.coe_nonneg) }
end


/-  I (DT) extracted this lemma to speed up the proof of `normed_snake_dual`.
The `ρ` in this lemma stands for `K + r₁ * r₂ * K * K'` in the application. -/
lemma exists_norm_sub_le_mul {M : system_of_complexes} {k k' c ρ : ℝ≥0}
  {i : ℕ}
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')]
  (hM_adm : M.admissible)
  (ex_le : (∀ (m : (M (k * (k' * c)) i)),
        (∃ (i₀ : ℕ) (hi₀ : i₀ = i - 1) (y : (M c i₀)),
           ∥res m - (M.d i₀ i) y∥ ≤ ↑ρ * ∥(M.d i (i + 1)) m∥)))
  (m₁ : (M (k * k' * c) i)) :
  ∃ (i₀ j : ℕ) (hi₀ : i₀ = i - 1) (hj : i + 1 = j) (y : (M c i₀)),
      ∥res m₁ - (M.d i₀ i) y∥ ≤ ↑ρ * ∥(M.d i j) m₁∥ :=
begin
  haveI : fact (k * (k' * c) ≤ k * k' * c) := { out := (mul_assoc _ _ _).symm.le },
  rcases ex_le (res m₁) with ⟨i₀, rfl, y, hy⟩,
  rw [res_res, d_res] at hy,
  refine ⟨i - 1, _, rfl, rfl, _⟩,
  refine ⟨y, hy.trans (mul_le_mul_of_nonneg_left _ ρ.2)⟩,
  exact hM_adm.res_norm_noninc _ _ _ _ _,
end

/-  I (DT) extracted this lemma to speed up the proof of `normed_snake_dual`. -/
lemma norm_sub_le_mul_mul_norm {M N : system_of_complexes} {f : M ⟶ N}
  {k k' K c : ℝ≥0} (mK : ℝ≥0) {m : M (k * (k' * c)) 0} {n₁ : N (k' * c) 0} {m₁ : M c 0}
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')]
  (hfnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (M c i)), ∥(f.apply) x∥ = ∥x∥)
  (inadm : ∥((res (res m : (M (k' * c) 0))) : (M c 0))∥ ≤ ∥(res m : (M (k' * c) 0))∥ )
  (hn₁ : ∥res (f m) - (N.d 0 0) n₁∥ ≤ ↑K * ∥(N.d 0 (0 + 1)) (f m)∥) :
  ∥res m - (M.d 0 0) m₁∥ ≤ (K * (1 + mK)) * ∥(M.d 0 (0 + 1)) m∥ :=
begin
  simp only [d_self_apply, sub_zero, nnreal.coe_add, nnreal.coe_mul] at hn₁ ⊢,
  rw [res_apply, hom_apply f (res m), hfnorm] at hn₁,
  have new : fact (c ≤ k' * c) := { out := le_mul_of_one_le_left c.2 hk'.out },
  rw ←res_res _ _ _ new,
  refine le_trans inadm (le_trans hn₁ _),
  rw [d_apply, hom_apply f _, hfnorm],
  rw mul_assoc,
  refine (mul_le_mul_of_nonneg_left _ K.2),
  exact le_mul_of_one_le_left (norm_nonneg _) (le_add_of_nonneg_right mK.2),
end

/-  I (DT) extracted this lemma to speed up the proof of `normed_snake_dual`. -/
lemma norm_sub_le_mul_norm {k' K K' r₁ r₂ c c₁ : ℝ≥0}
  {i  : ℕ} (hii' : (i - 1) + 1 = i)
  [hk' : fact (1 ≤ k')]
  [fc₁ : fact (k' * c ≤ c₁)]
  [fc : fact (c ≤ c₁)]
  (hN_adm : N.admissible)
  (hgnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (N c i)), ∥g x∥ ≤ ↑r₁ * ∥x∥)
  (hfnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (M c i)), ∥(f.apply) x∥ = ∥x∥)
  {n₁ : N (k' * c) (i - 1)}
  {n₂ : N c (i - 1 - 1)}
  {nnew₁ : N c (i - 1)}
  {m₁ : M c (i - 1)}
  {m : (M c₁ i)}
  (hn₁ : ∥res (f m) - (N.d (i - 1) i) n₁∥ ≤ K * ∥(N.d i (i + 1)) (f m)∥)
  (hp₂ : ∥res (g n₁) - (P.d (i - 1 - 1) (i - 1)) (g n₂)∥ ≤ K' * ∥(P.d (i - 1) ((i - 1) + 1)) (g n₁)∥)
  (hnormnnew₁ : ∥nnew₁∥ ≤ r₂ * ∥g (res n₁ - ((N.d (i - 1 - 1) (i - 1)) n₂))∥)
  (hm₁ : f m₁ = res n₁ - ((N.d (i - 1 - 1) (i - 1)) n₂) - nnew₁)
  (hfm : ∥g ((N.d (i - 1) i) n₁)∥ = ∥g (res (f m) - (N.d (i - 1) i) n₁)∥) :
  ∥res m - (M.d (i - 1) i) m₁∥ ≤ (K + r₁ * r₂ * K * K') * ∥(M.d i (i + 1)) m∥ :=
begin
  rw ← add_zero (_ * ∥_∥) at ⊢ hn₁ hp₂,
  apply norm_sub_le_mul_norm_add M N P f g _ hN_adm hgnorm hfnorm _ _ hn₁ hp₂ hnormnnew₁ hm₁ hfm,
  { exact hii' },
  { rw [zero_mul, zero_div] },
  { rw [mul_zero, zero_div] },
end


#exit
lemma weak_normed_snake_dual (k k' K K' r₁ r₂ : ℝ≥0)
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')]
  {a : ℕ} {c₀ : ℝ≥0}
  (hN : N.is_weak_bounded_exact k K (a + 1) c₀)
  (hP : P.is_weak_bounded_exact k' K' (a + 1) c₀)
  (hN_adm : N.admissible)
  (hgnrm : ∀ c i (x : N c i), ∥g x∥ ≤ r₁ * ∥x∥)
  (Hg : ∀ (c : ℝ≥0) [fact (c₀ ≤ c)] (i : ℕ) (hi : i ≤ a + 1 + 1) (y : P c i),
    ∃ (x : N c i), g x = y ∧ ∥x∥ ≤ r₂ * ∥y∥)
  (hg : ∀ c i, (f.apply : M c i ⟶ N c i).range = g.apply.ker)
  (hf : ∀ c i, @isometry (M c i) (N c i) _ _ f.apply) :
  M.is_weak_bounded_exact (k * k') (K + r₁ * r₂ * K * K') a c₀ :=
begin
  introsI c hc i hi,
  apply exists_norm_sub_le_mul_add (admissible_of_isometry hN_adm hf),
  intros m ε hε,

  have hlt : 0 < (1 + K' * r₁ * r₂ : ℝ) :=
    add_pos_of_pos_of_nonneg zero_lt_one ((K' * r₁ * r₂).coe_nonneg),
  have hε₁ : 0 < ε / 2 * (1 + K' * r₁ * r₂)⁻¹ := mul_pos (half_pos hε) (inv_pos.2 hlt),
  obtain ⟨_, _, rfl, rfl, n₁, hn₁⟩ :=
    hN _ ⟨hc.out.trans $ le_mul_of_one_le_left' hk'.out⟩ _ (trans hi a.le_succ) (f m) _ hε₁,
  have Hi' : i - 1 ≤ a + 1 := trans i.pred_le (trans hi a.le_succ),
  obtain ⟨_, _, rfl, rfl, p₂, hp₂⟩ := hP _ hc _ Hi' (g n₁)
    (if (r₂ : ℝ) = 0 then 1 else (ε / 2) * r₂⁻¹) _,
  { have Hi'' : (i - 1 - 1) ≤ a + 1 + 1 := trans (nat.pred_le _) (trans Hi' (nat.le_succ _)),
    obtain ⟨n₂, rfl, hnormn₂⟩ := Hg c (i - 1 - 1) Hi'' p₂,
    let n₁' := N.d (i - 1 - 1) (i - 1) n₂,
    obtain ⟨nnew₁, hnnew₁, hnrmnew₁⟩ := Hg c (i - 1) (trans Hi' a.succ.le_succ) (g (res n₁ - n₁')),
    have hker : (res n₁ - n₁') - nnew₁ ∈ g.apply.ker,
    { rw [mem_ker, normed_group_hom.map_sub, sub_eq_zero, ←hom_apply, ←hom_apply, hnnew₁] },
    rw ←hg at hker,
    obtain ⟨m₁, hm₁ : f m₁ = res n₁ - n₁' - nnew₁⟩ := (mem_range _ _).1 hker,
    refine ⟨i - 1, rfl, m₁, _⟩,

    have hfnrm : ∀ c i (x : M c i), ∥f.apply x∥ = ∥x∥ :=
      λ c i x, (isometry_iff_norm _).1 (hf c i) x,
    by_cases hizero : i = 0,
    { subst hizero,
      convert norm_sub_le_mul_mul_norm_add (K' * r₁ * r₂) _ hfnrm _ hn₁,
      { norm_cast, ring },
      { exact ε₁_le_ε hε (K' * r₁ * r₂) rfl },
      { exact (admissible_of_isometry hN_adm hf).res_norm_noninc _ _ _ _ _ } },

    { refine norm_sub_le_mul_norm_add M N P f g _ hN_adm hgnrm hfnrm _ _ hn₁ hp₂ hnrmnew₁ hm₁ _,
      { exact nat.succ_pred_eq_of_pos (nat.pos_of_ne_zero hizero) },
      { field_simp [hlt.ne.symm], ring },
      { by_cases H : r₂ = 0,
        { simp only [H, nnreal.coe_zero, if_true, zero_mul, (half_pos hε).le], },
        { simp only [H, nnreal.coe_eq_zero, if_false, mul_comm,
            mul_inv_cancel_left' (nnreal.coe_ne_zero.mpr H)] } },
      { have : f (res m : M (k' * c) i) ∈ f.apply.range, { rw mem_range, exact ⟨res m, rfl⟩ },
        rw [hg, mem_ker] at this,
        rw [hom_apply g (res (f m) - (N.d (i - 1) i) n₁), res_apply, normed_group_hom.map_sub, this,
          zero_sub, norm_neg, ←hom_apply] } } },
  { by_cases H : r₂ = 0,
    { simp only [H, zero_lt_one, if_true, eq_self_iff_true, nnreal.coe_eq_zero] },
    { simp only [H, nnreal.coe_eq_zero, if_false],
      exact mul_pos (half_pos hε) (inv_pos.2 (nnreal.coe_pos.2 (zero_lt_iff.2 H))) } }
end

lemma normed_snake_dual {k k' K K' r₁ r₂ : ℝ≥0}
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')]
  {a : ℕ} {c₀ : ℝ≥0}
  (hN : N.is_bounded_exact k K (a + 1) c₀)
  (hP : P.is_bounded_exact k' K' (a + 1) c₀)
  (hN_adm : N.admissible)
  (hgnorm : ∀ c i (x : N c i), ∥g x∥ ≤ r₁ * ∥x∥)
  (Hg : ∀ (c : ℝ≥0) [fact (c₀ ≤ c)] (i : ℕ) (hi : i ≤ a + 1 + 1) (y : P c i),
    ∃ (x : N c i), g x = y ∧ ∥x∥ ≤ r₂ * ∥y∥)
  (hg : ∀ c i, (f.apply : M c i ⟶ N c i).range = g.apply.ker)
  (hf : ∀ c i, @isometry (M c i) (N c i) _ _ f.apply) :
  M.is_bounded_exact (k * k') (K + r₁ * r₂ * K * K') a c₀ :=
begin
  introsI c hc i hi,
  refine exists_norm_sub_le_mul (admissible_of_isometry hN_adm hf) _,

  intro m,

  obtain ⟨_, _, rfl, rfl, n₁, hn₁⟩ :=
    hN _ ⟨hc.out.trans $ le_mul_of_one_le_left' hk'.out⟩ _ (trans hi a.le_succ) (f m),
  have Hi' : (i - 1) ≤ a + 1 := trans i.pred_le (trans hi a.le_succ),
  obtain ⟨_, _, rfl, rfl, p₂, hp₂⟩ := hP _ hc _ Hi' (g n₁),
  have Hi'' : (i - 1 - 1) ≤ a + 1 + 1 := trans (nat.pred_le _) (trans Hi' (nat.le_succ _)),
  obtain ⟨n₂, rfl, hnormn₂⟩ := Hg c (i - 1 - 1) Hi'' p₂,
  let n₁' := N.d (i - 1 - 1) (i - 1) n₂,
  obtain ⟨nnew₁, hnnew₁, hnormnnew₁⟩ := Hg c (i - 1) (trans Hi' (nat.le_succ _)) (g (res n₁ - n₁')),
  have hker : (res n₁ - n₁') - nnew₁ ∈ g.apply.ker,
  { rw [mem_ker, normed_group_hom.map_sub, sub_eq_zero, ←hom_apply, ←hom_apply, hnnew₁] },
  rw ←hg at hker,
  obtain ⟨m₁, hm₁ : f m₁ = res n₁ - n₁' - nnew₁⟩ := (mem_range _ _).1 hker,
  refine ⟨i - 1, rfl, m₁, _⟩,

  have hfnorm : ∀ c i (x : M c i), ∥f.apply x∥ = ∥x∥ := λ c i x, (isometry_iff_norm _).1 (hf c i) x,
  by_cases hizero : i = 0,
  { subst hizero,
    convert norm_sub_le_mul_mul_norm (K' * r₁ * r₂) hfnorm _ hn₁,
    { norm_cast, ring },
    { exact (admissible_of_isometry hN_adm hf).res_norm_noninc _ _ _ _ _ } },

  have hii' : i - 1 + 1 = i,
  { rw [nat.sub_one, nat.add_one, nat.succ_pred_eq_of_pos (zero_lt_iff.mpr hizero)] },
  have hfm : ∥g (N.d (i - 1) i n₁)∥ = ∥g (res (f m) - N.d (i - 1) i n₁)∥,
  { have : f (@res _ _ (k' * c) _ _ m) ∈ f.apply.range := by { rw mem_range, exact ⟨res m, rfl⟩ },
    rw [hg, mem_ker] at this,
    rw [hom_apply g (res (f m) - (N.d _ i) n₁), res_apply, normed_group_hom.map_sub, this,
      zero_sub, norm_neg, ←hom_apply] },
  exact norm_sub_le_mul_norm M N P f g hii' hN_adm hgnorm hfnorm hn₁ hp₂ hnormnnew₁ hm₁ hfm,
end







#exit
import system_of_complexes.basic

universe variables u

noncomputable theory
open_locale nnreal
open category_theory opposite normed_group_hom system_of_complexes


variables (M N P : system_of_complexes.{u}) (f : M ⟶ N) (g : N ⟶ P)

set_option profiler true

/-  I (DT) extracted this lemma to speed up the proof of `weak_normed_snake_dual`. -/
/-  Already allows `ε = 0`. -/
lemma norm_sub_le_mul_norm_add {k' K K' r₁ r₂ c c₁ : ℝ≥0} {ε ε₁ ε₂ : ℝ}
  {i i' i'' : ℕ} (hii' : i' + 1 = i)
  [hk' : fact (1 ≤ k')]
  [fc₁ : fact (k' * c ≤ c₁)]
  [fc : fact (c ≤ c₁)]
  (hN_adm : N.admissible)
  (hgnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (N c i)), ∥g x∥ ≤ ↑r₁ * ∥x∥)
  (hfnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (M c i)), ∥(f.apply) x∥ = ∥x∥)
  {n₁ : N (k' * c) i'}
  {n₂ : N c i''}
  {nnew₁ : N c i'}
  {m₁ : M c i'}
  {m : (M c₁ i)}
  (hmulε₁ : ε₁ * (1 + K' * r₁ * r₂) = ε / 2)
  (hle : (r₂ : ℝ) * ε₂ ≤ ε / 2)
  (hn₁ : ∥res (f m) - (N.d i' i) n₁∥ ≤ K * ∥(N.d i (i + 1)) (f m)∥ + ε₁)
  (hp₂ : ∥res (g n₁) - (P.d i'' i') (g n₂)∥ ≤ K' * ∥(P.d i' (i' + 1)) (g n₁)∥ + ε₂)
  (hnormnnew₁ : ∥nnew₁∥ ≤ r₂ * ∥g (res n₁ - ((N.d i'' i') n₂))∥)
  (hm₁ : f m₁ = res n₁ - ((N.d i'' i') n₂) - nnew₁)
  (hfm : ∥g ((N.d i' i) n₁)∥ = ∥g (res (f m) - (N.d i' i) n₁)∥) :
  ∥res m - (M.d i' i) m₁∥ ≤ (K + r₁ * r₂ * K * K') * ∥(M.d i (i + 1)) m∥ + ε :=
sorry

/-  I (DT) extracted this lemma to speed up the proof of `weak_normed_snake_dual`.
The `ρ` in this lemma stands for `K + r₁ * r₂ * K * K'` in the application. -/
/-  Not switched order of `∀` in `ex_le`. -/
lemma exists_norm_sub_le_mul_add {M : system_of_complexes} {k k' c ρ : ℝ≥0}
  {i : ℕ}
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')]
  (hM_adm : M.admissible)
  (ex_le : (∀ (m : M (k * (k' * c)) i), ∀ (ε : ℝ), 0 < ε →
        (∃ (i₀ : ℕ) (hi₀ : i₀ = i - 1) (y : (M c i₀)),
           ∥res m - (M.d i₀ i) y∥ ≤ ↑ρ * ∥(M.d i (i + 1)) m∥ + ε)))
  (m₁ : (M (k * k' * c) i))
  {ε : ℝ}
  (hε : 0 < ε) :
  ∃ (i₀ j : ℕ) (hi₀ : i₀ = i - 1) (hj : i + 1 = j) (y : (M c i₀)),
      ∥res m₁ - (M.d i₀ i) y∥ ≤ ↑ρ * ∥(M.d i j) m₁∥ + ε :=
begin
  haveI : fact (k * (k' * c) ≤ k * k' * c) := { out := (mul_assoc _ _ _).symm.le },
  rcases ex_le (res m₁) ε hε with ⟨i₀, rfl, y, hy⟩,
  rw [res_res, d_res] at hy,
  refine ⟨i - 1, _, rfl, rfl, _⟩,
  refine ⟨y, hy.trans (add_le_add_right (mul_le_mul_of_nonneg_left _ ρ.2) ε)⟩,
  exact hM_adm.res_norm_noninc _ _ _ _ _,
end

/-  I (DT) extracted this lemma to speed up the proof of `normed_snake_dual`.
The `ρ` in this lemma stands for `K + r₁ * r₂ * K * K'` in the application. -/
/- Proven as a consequence of what is above. -/
lemma exists_norm_sub_le_mul {M : system_of_complexes} {k k' c ρ : ℝ≥0}
  {i : ℕ}
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')]
  (hM_adm : M.admissible)
  (ex_le : (∀ (m : (M (k * (k' * c)) i)),
        (∃ (i₀ : ℕ) (hi₀ : i₀ = i - 1) (y : (M c i₀)),
           ∥res m - (M.d i₀ i) y∥ ≤ ↑ρ * ∥(M.d i (i + 1)) m∥)))
  (m₁ : (M (k * k' * c) i)) :
  ∃ (i₀ j : ℕ) (hi₀ : i₀ = i - 1) (hj : i + 1 = j) (y : (M c i₀)),
      ∥res m₁ - (M.d i₀ i) y∥ ≤ ↑ρ * ∥(M.d i j) m₁∥ :=
begin
  --unfreezingI{
  obtain m₂ : (M (k * (k' * c)) i) := by { rwa mul_assoc at m₁ },
  have : (M (k * k' * c) i) = (M (k * (k' * c)) i),
  { rw mul_assoc },
  let m₁' := m₁,
  have : m₁ = m₁' := rfl,
  rw this at m₁',

  obtain ⟨_, rfl, y, hy⟩ := ex_le (by {rw mul_assoc at m₁, exact m₂}),
  refine ⟨_, _, rfl, rfl, y, _⟩,
  convert hy,

  --},


--  obtain F := exists_norm_sub_le_mul_add hM_adm _ m₁ _,
  obtain F := (exists_norm_sub_le_mul_add hM_adm _) m₁,


  rcases F m₁ with ⟨F_h_w, F_h_h_w, ⟨⟩, rfl, y, hy⟩,
  refine ⟨i - 1, i + 1, rfl, rfl, y, _⟩,
  {
    apply le_iff_forall_pos_le_add.mpr,
  }
--  rw mul_assoc at m₁,
--  obtain G := ex_le m₁,
--  convert G,simp,
  haveI : fact (k * (k' * c) ≤ k * k' * c) := { out := (mul_assoc _ _ _).symm.le },
  rcases ex_le (res m₁) with ⟨i₀, rfl, y, hy⟩,
  rw [res_res, d_res] at hy,
  refine ⟨i - 1, _, rfl, rfl, _⟩,
  refine ⟨y, hy.trans (mul_le_mul_of_nonneg_left _ ρ.2)⟩,
  exact hM_adm.res_norm_noninc _ _ _ _ _,
end

#exit














/-  I (DT) extracted this lemma to speed up the proof of `normed_snake_dual`.
The `ρ` in this lemma stands for `K + r₁ * r₂ * K * K'` in the application. -/
lemma exists_norm_sub_le_mul {M : system_of_complexes} {k k' c ρ : ℝ≥0}
  {i : ℕ}
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')]
  (hM_adm : M.admissible)
  (ex_le : (∀ (m : (M (k * (k' * c)) i)),
        (∃ (i₀ : ℕ) (hi₀ : i₀ = i - 1) (y : (M c i₀)),
           ∥res m - (M.d i₀ i) y∥ ≤ ↑ρ * ∥(M.d i (i + 1)) m∥)))
  (m₁ : (M (k * k' * c) i)) :
  ∃ (i₀ j : ℕ) (hi₀ : i₀ = i - 1) (hj : i + 1 = j) (y : (M c i₀)),
      ∥res m₁ - (M.d i₀ i) y∥ ≤ ↑ρ * ∥(M.d i j) m₁∥ :=
begin
  haveI : fact (k * (k' * c) ≤ k * k' * c) := { out := (mul_assoc _ _ _).symm.le },
  rcases ex_le (res m₁) with ⟨i₀, rfl, y, hy⟩,
  rw [res_res, d_res] at hy,
  refine ⟨i - 1, _, rfl, rfl, _⟩,
  refine ⟨y, hy.trans (mul_le_mul_of_nonneg_left _ ρ.2)⟩,
  exact hM_adm.res_norm_noninc _ _ _ _ _,
end

/-  I (DT) extracted this lemma to speed up the proof of `normed_snake_dual`. -/
lemma norm_sub_le_mul_mul_norm {M N : system_of_complexes} {f : M ⟶ N}
  {k k' K c : ℝ≥0} (mK : ℝ≥0) {m : M (k * (k' * c)) 0} {n₁ : N (k' * c) 0} {m₁ : M c 0}
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')]
  (hfnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (M c i)), ∥(f.apply) x∥ = ∥x∥)
  (inadm : ∥((res (res m : (M (k' * c) 0))) : (M c 0))∥ ≤ ∥(res m : (M (k' * c) 0))∥ )
  (hn₁ : ∥res (f m) - (N.d 0 0) n₁∥ ≤ ↑K * ∥(N.d 0 (0 + 1)) (f m)∥) :
  ∥res m - (M.d 0 0) m₁∥ ≤ (K * (1 + mK)) * ∥(M.d 0 (0 + 1)) m∥ :=
begin
  simp only [d_self_apply, sub_zero, nnreal.coe_add, nnreal.coe_mul] at hn₁ ⊢,
  rw [res_apply, hom_apply f (res m), hfnorm] at hn₁,
  have new : fact (c ≤ k' * c) := { out := le_mul_of_one_le_left c.2 hk'.out },
  rw ←res_res _ _ _ new,
  refine le_trans inadm (le_trans hn₁ _),
  rw [d_apply, hom_apply f _, hfnorm],
  rw mul_assoc,
  refine (mul_le_mul_of_nonneg_left _ K.2),
  exact le_mul_of_one_le_left (norm_nonneg _) (le_add_of_nonneg_right mK.2),
end







lemma exists_norm_sub_le_mul {M : system_of_complexes} {k k' c ρ : ℝ≥0}
  {i : ℕ}
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')]
  (hM_adm : M.admissible)
  (ex_le : (∀ (m : (M (k * (k' * c)) i)),
        (∃ (i₀ : ℕ) (hi₀ : i₀ = i - 1) (y : (M c i₀)),
           ∥res m - (M.d i₀ i) y∥ ≤ ↑ρ * ∥(M.d i (i + 1)) m∥)))
  (m₁ : (M (k * k' * c) i)) :
  ∃ (i₀ j : ℕ) (hi₀ : i₀ = i - 1) (hj : i + 1 = j) (y : (M c i₀)),
      ∥res m₁ - (M.d i₀ i) y∥ ≤ ↑ρ * ∥(M.d i j) m₁∥ :=
sorry

lemma weak_normed_snake_dual (k k' K K' r₁ r₂ : ℝ≥0)
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')]
  {a : ℕ} {c₀ : ℝ≥0}
  (hN : N.is_weak_bounded_exact k K (a + 1) c₀)
  (hP : P.is_weak_bounded_exact k' K' (a + 1) c₀)
  (hN_adm : N.admissible)
  (hgnrm : ∀ c i (x : N c i), ∥g x∥ ≤ r₁ * ∥x∥)
  (Hg : ∀ (c : ℝ≥0) [fact (c₀ ≤ c)] (i : ℕ) (hi : i ≤ a + 1 + 1) (y : P c i),
    ∃ (x : N c i), g x = y ∧ ∥x∥ ≤ r₂ * ∥y∥)
  (hg : ∀ c i, (f.apply : M c i ⟶ N c i).range = g.apply.ker)
  (hf : ∀ c i, @isometry (M c i) (N c i) _ _ f.apply) :
  M.is_weak_bounded_exact (k * k') (K + r₁ * r₂ * K * K') a c₀ :=
sorry



#exit
/-  I (DT) extracted this lemma to speed up the proof of `weak_normed_snake_dual`. -/
/-
lemma ε₁_pos (a : ℝ≥0) {ε ε₁ : ℝ} (hε : 0 < ε) (hmulε : ε₁ * (1 + a) = ε / 2) :
  0 < ε₁ :=
have one_add_pos : (0 : ℝ) < 1 + a := add_pos_of_pos_of_nonneg zero_lt_one (zero_le a),
calc 0 < ε / 2 / (1 + ↑a) : div_pos (half_pos hε) one_add_pos
       ... = _ : ((eq_div_iff one_add_pos.ne').mpr hmulε).symm

/-  I (DT) extracted this lemma to speed up the proof of `weak_normed_snake_dual`. -/
lemma norm_sub_le_mul_norm_add {k' K K' r₁ r₂ c c₁ : ℝ≥0} {ε ε₁ ε₂ : ℝ}
  {i i' i'' : ℕ} (hii' : i' + 1 = i)
  [hk' : fact (1 ≤ k')]
  [fc₁ : fact (k' * c ≤ c₁)]
  [fc : fact (c ≤ c₁)]
  (hN_adm : N.admissible)
  (hgnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (N c i)), ∥g x∥ ≤ ↑r₁ * ∥x∥)
  (hfnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (M c i)), ∥(f.apply) x∥ = ∥x∥)
  {n₁ : N (k' * c) i'}
  {n₂ : N c i''}
  {nnew₁ : N c i'}
  {m₁ : M c i'}
  {m : (M c₁ i)}
  (hmulε₁ : ε₁ * (1 + K' * r₁ * r₂) = ε / 2)
  (hle : (r₂ : ℝ) * ε₂ ≤ ε / 2)
  (hn₁ : ∥res (f m) - (N.d i' i) n₁∥ ≤ K * ∥(N.d i (i + 1)) (f m)∥ + ε₁)
  (hp₂ : ∥res (g n₁) - (P.d i'' i') (g n₂)∥ ≤ K' * ∥(P.d i' (i' + 1)) (g n₁)∥ + ε₂)
  (hnormnnew₁ : ∥nnew₁∥ ≤ r₂ * ∥g (res n₁ - ((N.d i'' i') n₂))∥)
  (hm₁ : f m₁ = res n₁ - ((N.d i'' i') n₂) - nnew₁)
  (hfm : ∥g ((N.d i' i) n₁)∥ = ∥g (res (f m) - (N.d i' i) n₁)∥) :
  ∥res m - (M.d i' i) m₁∥ ≤ (K + r₁ * r₂ * K * K') * ∥(M.d i (i + 1)) m∥ + ε :=
calc ∥res m - (M.d i' i) m₁∥ = ∥f (res m - (M.d i' i) m₁)∥ : (hfnorm _ _ _).symm
  ... = ∥res _ - (N.d i' i (res n₁) - N.d i' i (_ + nnew₁))∥ :
    by rw [hom_apply, normed_group_hom.map_sub, ←hom_apply, ←hom_apply, ←res_apply,
    ←d_apply, hm₁, sub_sub, normed_group_hom.map_sub]
  ... = ∥(res _ - N.d i' i (res n₁)) + N.d i' i (_ + nnew₁)∥ : by abel
  ... ≤ ∥res _ - N.d i' i _∥ + ∥N.d i' i (_ + nnew₁)∥ : norm_add_le _ _
  ... = ∥res _ - N.d i' i _∥ + ∥N.d i' i nnew₁∥ : by simp only [map_add, zero_add, d_d]
  ... ≤ ∥res _ - N.d i' i _∥ + r₂ * ∥g (res n₁ - _)∥ :
    add_le_add_left (le_trans (hN_adm.d_norm_noninc _ _ i' i nnew₁) hnormnnew₁) _
  ... = ∥res _ - N.d i' i _∥ + r₂ * ∥res _ - P.d i'' i' (g n₂)∥ :
    by rw [hom_apply g, normed_group_hom.map_sub, ←hom_apply, ←hom_apply,
    ←res_apply _ _ g, ←d_apply]
  ... ≤ ∥res _ - N.d i' i _∥ + r₂ * (K' * ∥P.d i' (i'+1) _∥ + ε₂) :
  add_le_add_left (mul_le_mul_of_nonneg_left hp₂ r₂.coe_nonneg) _
  ... = _ + r₂ * (K' * ∥P.d i' (i'+1) _∥ + ε₂) :
    by rw [←res_res, d_res, normed_group_hom.map_sub]
  ... ≤ K * _ + ε₁ + r₂ * (K' * ∥P.d i' (i'+1) _∥ + ε₂) :
  add_le_add_right (le_trans (hN_adm.res_norm_noninc _ _ _ _ _) hn₁) _
  ... = K * _ + ε₁ + r₂ * (K' * ∥g (res (f m) - N.d i' i n₁)∥ + ε₂) :
    by rw [d_apply _ _ g _, hii', hfm]
  ... ≤ K * _ + ε₁ + r₂ * (K' * (r₁ * ∥res (f m) - N.d i' i n₁∥) + ε₂) :
    add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left
      (hgnorm _ _ _) K'.coe_nonneg) _) $ r₂.coe_nonneg) _
  ... = K * _ + ε₁ + r₂ * (K' * r₁ * ∥res _ - N.d i' i n₁∥ + ε₂) : by rw mul_assoc
  ... ≤ K * _ + ε₁ + r₂ * (K' * r₁ * (K * ∥(N.d i (i+1)) _∥ + ε₁) + ε₂) :
    add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left
    hn₁ $ mul_nonneg K'.coe_nonneg r₁.coe_nonneg) _) r₂.coe_nonneg) _
  ... = (K + r₁ * r₂ * K * K') * ∥N.d i (i+1) (f m)∥ + ε₁ * (1 + K' * r₁ * r₂) + r₂ * ε₂ : by ring
  ... = (K + r₁ * r₂ * K * K') * ∥N.d i (i+1) (f m)∥ + ε / 2 + r₂ * ε₂ : by rw [hmulε₁]
  ... ≤ _ * ∥N.d i (i+1) (f m)∥ + ε / 2 + ε / 2 : add_le_add_left hle _
  ... = _ * ∥(M.d i (i+1)) m∥ + ε : by rw [add_assoc, add_halves', d_apply, hom_apply, hfnorm]


/-  I (DT) extracted this lemma to speed up the proof of `weak_normed_snake_dual`.
The `ρ` in this lemma stands for `K + r₁ * r₂ * K * K'` in the application. -/
lemma exists_norm_sub_le_mul_add {M : system_of_complexes} {k k' c ρ : ℝ≥0}
  {i : ℕ}
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')]
  (hM_adm : M.admissible)
  (ex_le : (∀ (m : (M (k * (k' * c)) i)) (ε : ℝ), 0 < ε →
        (∃ (i₀ : ℕ) (hi₀ : i₀ = i - 1) (y : (M c i₀)),
           ∥res m - (M.d i₀ i) y∥ ≤ ↑ρ * ∥(M.d i (i + 1)) m∥ + ε)))
  (m₁ : (M (k * k' * c) i))
  {ε : ℝ}
  (hε : 0 < ε) :
  ∃ (i₀ j : ℕ) (hi₀ : i₀ = i - 1) (hj : i + 1 = j) (y : (M c i₀)),
      ∥res m₁ - (M.d i₀ i) y∥ ≤ ↑ρ * ∥(M.d i j) m₁∥ + ε :=
begin
  haveI : fact (k * (k' * c) ≤ k * k' * c) := { out := (mul_assoc _ _ _).symm.le },
  rcases ex_le (res m₁) ε hε with ⟨i₀, rfl, y, hy⟩,
  rw [res_res, d_res] at hy,
  refine ⟨i - 1, _, rfl, rfl, _⟩,
  refine ⟨y, hy.trans (add_le_add_right (mul_le_mul_of_nonneg_left _ ρ.2) ε)⟩,
  exact hM_adm.res_norm_noninc _ _ _ _ _,
end


/-  I (DT) extracted this lemma to speed up the proof of `weak_normed_snake_dual`. -/
lemma norm_sub_le_mul_mul_norm_add {M N : system_of_complexes} {f : M ⟶ N}
  {k k' K c : ℝ≥0} (mK : ℝ≥0) {ε ε₁ : ℝ} {m : M (k * (k' * c)) 0} {n₁ : N (k' * c) 0} {m₁ : M c 0}
  (ee1 : ε₁ ≤ ε)
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')]
  (hfnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (M c i)), ∥(f.apply) x∥ = ∥x∥)
  (inadm : ∥((res (res m : (M (k' * c) 0))) : (M c 0))∥ ≤ ∥(res m : (M (k' * c) 0))∥ )
  (hn₁ : ∥res (f m) - (N.d 0 0) n₁∥ ≤ ↑K * ∥(N.d 0 (0 + 1)) (f m)∥ + ε₁) :
  ∥res m - (M.d 0 0) m₁∥ ≤ (K * (1 + mK)) * ∥(M.d 0 (0 + 1)) m∥ + ε :=
begin
  simp only [d_self_apply, sub_zero, nnreal.coe_add, nnreal.coe_mul] at hn₁ ⊢,
  rw [res_apply, hom_apply f (res m), hfnorm] at hn₁,
  have new : fact (c ≤ k' * c) := { out := le_mul_of_one_le_left c.2 hk'.out },
  rw ←res_res _ _ _ new,
  refine le_trans inadm (le_trans hn₁ _),
  rw [d_apply, hom_apply f _, hfnorm],
  refine add_le_add _ ee1,
  rw mul_assoc,
  refine (mul_le_mul_of_nonneg_left _ K.2),
  exact le_mul_of_one_le_left (norm_nonneg _) (le_add_of_nonneg_right mK.2),
end

/-  I (DT) extracted this lemma to speed up the proof of `weak_normed_snake_dual`. -/
lemma ε₁_le_ε {ε ε₁ : ℝ} (hε : 0 < ε) (mK : ℝ≥0) (hε₁ : ε₁ = ε / 2 * (1 + mK)⁻¹) :
  ε₁ ≤ ε :=
begin
  rw [hε₁, div_eq_mul_inv, mul_assoc, ← mul_inv'],
  refine mul_le_of_le_one_right (le_of_lt hε) _,
  rw mul_inv',
  refine mul_le_one nnreal.two_inv_lt_one.le (inv_nonneg.mpr (add_nonneg zero_le_one _)) _,
  { exact mK.coe_nonneg },
  { exact inv_le_one (le_add_of_nonneg_right mK.coe_nonneg) }
end
-/



/-  I (DT) extracted this lemma to speed up the proof of `normed_snake_dual`. -/
lemma norm_sub_le_mul_norm {k' K K' r₁ r₂ c c₁ : ℝ≥0}
  {i  : ℕ} (hii' : (i - 1) + 1 = i)
  [hk' : fact (1 ≤ k')]
  [fc₁ : fact (k' * c ≤ c₁)]
  [fc : fact (c ≤ c₁)]
  (hN_adm : N.admissible)
  (hgnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (N c i)), ∥g x∥ ≤ ↑r₁ * ∥x∥)
  (hfnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (M c i)), ∥(f.apply) x∥ = ∥x∥)
  {n₁ : N (k' * c) (i - 1)}
  {n₂ : N c (i - 1 - 1)}
  {nnew₁ : N c (i - 1)}
  {m₁ : M c (i - 1)}
  {m : (M c₁ i)}
  (hn₁ : ∥res (f m) - (N.d (i - 1) i) n₁∥ ≤ K * ∥(N.d i (i + 1)) (f m)∥)
  (hp₂ : ∥res (g n₁) - (P.d (i - 1 - 1) (i - 1)) (g n₂)∥ ≤ K' * ∥(P.d (i - 1) ((i - 1) + 1)) (g n₁)∥)
  (hnormnnew₁ : ∥nnew₁∥ ≤ r₂ * ∥g (res n₁ - ((N.d (i - 1 - 1) (i - 1)) n₂))∥)
  (hm₁ : f m₁ = res n₁ - ((N.d (i - 1 - 1) (i - 1)) n₂) - nnew₁)
  (hfm : ∥g ((N.d (i - 1) i) n₁)∥ = ∥g (res (f m) - (N.d (i - 1) i) n₁)∥) :
  ∥res m - (M.d (i - 1) i) m₁∥ ≤ (K + r₁ * r₂ * K * K') * ∥(M.d i (i + 1)) m∥ :=
begin
  set n₁' := N.d (i - 1 - 1) (i - 1) n₂ with hdefn₁',
  exact calc
  ∥res m - (M.d (i - 1) i) m₁∥ = ∥f (res m - (M.d _ i) m₁)∥ : (hfnorm _ _ _).symm
  ... = ∥res (f m) - (N.d _ i (res n₁) - N.d _ i (n₁' + nnew₁))∥ :
      by rw [hom_apply, normed_group_hom.map_sub, ←hom_apply, ←hom_apply, ←res_apply, ←d_apply, hm₁,
        sub_sub, normed_group_hom.map_sub]
  ... = ∥(res (f m) - N.d _ i (res n₁)) + N.d _ i (n₁' + nnew₁)∥ :
      by rw [sub_eq_add_neg, neg_sub, sub_add_eq_add_sub, add_sub]
  ... ≤ _ + ∥N.d _ i (n₁' + nnew₁)∥ : norm_add_le _ _
  ... = _ + ∥N.d _ i nnew₁∥ : by simp only [map_add, zero_add, d_d]
  ... ≤ _ + r₂ * ∥g (res n₁ - n₁')∥ :
      add_le_add_left (le_trans (hN_adm.d_norm_noninc _ _ _ i nnew₁) hnormnnew₁) _
  ... = ∥res (f m) - (N.d (i - 1) i) (res n₁)∥ + r₂ * ∥res (g n₁) - P.d (i - 1 - 1) _ (g n₂)∥ :
      by rw [hom_apply g, normed_group_hom.map_sub, ←hom_apply, ←hom_apply, ←res_apply, hdefn₁', ←d_apply]
  ... ≤ _ + r₂ * (K' * ∥P.d _ (_+1) (g n₁)∥) :
      add_le_add_left (mul_le_mul_of_nonneg_left hp₂ r₂.coe_nonneg) _
  ... = ∥@res _ _ c _ _ (@res _ _ _ _ _ (f m) - N.d _ i n₁)∥ + r₂ * (K' * ∥P.d _ (_+1) (g n₁)∥) :
      by rw [←@res_res _ _ _ c _ _ _ (f m), d_res, normed_group_hom.map_sub]
  ... ≤ K * ∥N.d i (i+1) _∥ + r₂ * (K' * ∥P.d _ (_+1) (g n₁)∥) :
      add_le_add_right (le_trans (hN_adm.res_norm_noninc _ _ _ _ _) hn₁) _
  ... = K * ∥N.d i (i+1) _∥ + r₂ * (K' * ∥g (res (f m) - N.d _ i n₁)∥) :
      by rw [d_apply _ _ g _, hii', hfm]
  ... ≤ K * ∥N.d i (i+1) _∥ + r₂ * (K' * (r₁ * ∥res (f m) - N.d _ i n₁∥)) :
      add_le_add_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (hgnorm _ _ _) $ nnreal.coe_nonneg K') $ nnreal.coe_nonneg r₂) _
  ... = K * ∥N.d i (i+1) (f m)∥ + r₂ * (K' * r₁ * ∥res (f m) - N.d _ i n₁∥) : by rw mul_assoc
  ... ≤ K * ∥N.d i (i+1) (f m)∥ + r₂ * (K' * r₁ * (K * ∥(N.d i (i+1)) _∥)) :
      add_le_add_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        hn₁ $ mul_nonneg K'.coe_nonneg r₁.coe_nonneg) r₂.coe_nonneg) _
  ... = (K + r₁ * r₂ * K * K') * ∥N.d i (i+1) (f m)∥ : by ring
  ... = _ * ∥(M.d i (i+1)) m∥ :
      by { rw d_apply _ _ f, simp only [hom_apply, hfnorm, nnreal.coe_add, nnreal.coe_mul] }
end



lemma normed_snake_dual {k k' K K' r₁ r₂ : ℝ≥0}
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')]
  {a : ℕ} {c₀ : ℝ≥0}
  (hN : N.is_bounded_exact k K (a + 1) c₀)
  (hP : P.is_bounded_exact k' K' (a + 1) c₀)
  (hN_adm : N.admissible)
  (hgnorm : ∀ c i (x : N c i), ∥g x∥ ≤ r₁ * ∥x∥)
  (Hg : ∀ (c : ℝ≥0) [fact (c₀ ≤ c)] (i : ℕ) (hi : i ≤ a + 1 + 1) (y : P c i),
    ∃ (x : N c i), g x = y ∧ ∥x∥ ≤ r₂ * ∥y∥)
  (hg : ∀ c i, (f.apply : M c i ⟶ N c i).range = g.apply.ker)
  (hf : ∀ c i, @isometry (M c i) (N c i) _ _ f.apply) :
  M.is_bounded_exact (k * k') (K + r₁ * r₂ * K * K') a c₀ :=
begin
  introsI c hc i hi,
  refine exists_norm_sub_le_mul (admissible_of_isometry hN_adm hf) _,

  intro m,

  obtain ⟨_, _, rfl, rfl, n₁, hn₁⟩ :=
    hN _ ⟨hc.out.trans $ le_mul_of_one_le_left' hk'.out⟩ _ (trans hi a.le_succ) (f m),
  have Hi' : (i - 1) ≤ a + 1 := trans i.pred_le (trans hi a.le_succ),
  obtain ⟨_, _, rfl, rfl, p₂, hp₂⟩ := hP _ hc _ Hi' (g n₁),
  have Hi'' : (i - 1 - 1) ≤ a + 1 + 1 := trans (nat.pred_le _) (trans Hi' (nat.le_succ _)),
  obtain ⟨n₂, rfl, hnormn₂⟩ := Hg c (i - 1 - 1) Hi'' p₂,
  let n₁' := N.d (i - 1 - 1) (i - 1) n₂,
  obtain ⟨nnew₁, hnnew₁, hnormnnew₁⟩ := Hg c (i - 1) (trans Hi' (nat.le_succ _)) (g (res n₁ - n₁')),
  have hker : (res n₁ - n₁') - nnew₁ ∈ g.apply.ker,
  { rw [mem_ker, normed_group_hom.map_sub, sub_eq_zero, ←hom_apply, ←hom_apply, hnnew₁] },
  rw ←hg at hker,
  obtain ⟨m₁, hm₁ : f m₁ = res n₁ - n₁' - nnew₁⟩ := (mem_range _ _).1 hker,
  refine ⟨i - 1, rfl, m₁, _⟩,

  have hfnorm : ∀ c i (x : M c i), ∥f.apply x∥ = ∥x∥ := λ c i x, (isometry_iff_norm _).1 (hf c i) x,
  by_cases hizero : i = 0,
  { subst hizero,
    convert norm_sub_le_mul_mul_norm (K' * r₁ * r₂) hfnorm _ hn₁,
    { norm_cast, ring },
    { exact (admissible_of_isometry hN_adm hf).res_norm_noninc _ _ _ _ _ } },

  have hii' : i - 1 + 1 = i,
  { rw [nat.sub_one, nat.add_one, nat.succ_pred_eq_of_pos (zero_lt_iff.mpr hizero)] },
  have hfm : ∥g (N.d (i - 1) i n₁)∥ = ∥g (res (f m) - N.d (i - 1) i n₁)∥,
  { have : f (@res _ _ (k' * c) _ _ m) ∈ f.apply.range := by { rw mem_range, exact ⟨res m, rfl⟩ },
    rw [hg, mem_ker] at this,
    rw [hom_apply g (res (f m) - (N.d _ i) n₁), res_apply, normed_group_hom.map_sub, this,
      zero_sub, norm_neg, ←hom_apply] },
  exact norm_sub_le_mul_norm M N P f g hii' hN_adm hgnorm hfnorm hn₁ hp₂ hnormnnew₁ hm₁ hfm,
end

#exit

import system_of_complexes.basic

universe variables u

noncomputable theory
open_locale nnreal
open category_theory opposite normed_group_hom system_of_complexes


variables (M N P : system_of_complexes.{u}) (f : M ⟶ N) (g : N ⟶ P)
/-  I (DT) extracted this lemma to speed up the proof of `weak_normed_snake_dual`. -/
lemma ε₁_pos (a : ℝ≥0) {ε ε₁ : ℝ} (hε : 0 < ε) (hmulε : ε₁ * (1 + a) = ε / 2) :
  0 < ε₁ :=
have one_add_pos : (0 : ℝ) < 1 + a := add_pos_of_pos_of_nonneg zero_lt_one (zero_le a),
calc 0 < ε / 2 / (1 + ↑a) : div_pos (half_pos hε) one_add_pos
       ... = _ : ((eq_div_iff one_add_pos.ne').mpr hmulε).symm

/-  I (DT) extracted this lemma to speed up the proof of `weak_normed_snake_dual`. -/
lemma norm_sub_le_mul_norm_add {k' K K' r₁ r₂ c c₁ : ℝ≥0}
  {ε ε₁ ε₂ : ℝ} (hε : 0 < ε)
  {i i' i'' : ℕ} (hii' : i' + 1 = i)
  [hk' : fact (1 ≤ k')]
  [fc₁ : fact (k' * c ≤ c₁)]
  [fc : fact (c ≤ c₁)]
  (hN_adm : N.admissible)
  (hgnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (N c i)), ∥g x∥ ≤ ↑r₁ * ∥x∥)
  (hfnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (M c i)), ∥(f.apply) x∥ = ∥x∥)
  {n₁ : N (k' * c) i'}
  {n₂ : N c i''}
  {nnew₁ : N c i'}
  {m₁ : M c i'}
  {m : (M c₁ i)}
  (hmulε₁ : ε₁ * (1 + K' * r₁ * r₂) = ε / 2)
  (hle : (r₂ : ℝ) * ε₂ ≤ ε / 2)
  (hn₁ : ∥res (f m) - (N.d i' i) n₁∥ ≤ K * ∥(N.d i (i + 1)) (f m)∥ + ε₁)
  (hp₂ : ∥res (g n₁) - (P.d i'' i') (g n₂)∥ ≤ K' * ∥(P.d i' (i' + 1)) (g n₁)∥ + ε₂)
  (hnormnnew₁ : ∥nnew₁∥ ≤ r₂ * ∥g (res n₁ - ((N.d i'' i') n₂))∥)
  (hm₁ : f m₁ = res n₁ - ((N.d i'' i') n₂) - nnew₁)
  (hfm : ∥g ((N.d i' i) n₁)∥ = ∥g (res (f m) - (N.d i' i) n₁)∥) :
  ∥res m - (M.d i' i) m₁∥ ≤ (K + r₁ * r₂ * K * K') * ∥(M.d i (i + 1)) m∥ + ε :=
sorry

lemma norm_sub_le_mul_norm_add_1 {k' K K' r₁ r₂ c c₁ : ℝ≥0}
  --{ε ε₁ ε₂ : ℝ} (hε : 0 < ε)
  {i i' i'' : ℕ} (hii' : i' + 1 = i)
  [hk' : fact (1 ≤ k')]
  [fc₁ : fact (k' * c ≤ c₁)]
  [fc : fact (c ≤ c₁)]
  (hN_adm : N.admissible)
  (hgnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (N c i)), ∥g x∥ ≤ ↑r₁ * ∥x∥)
  (hfnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (M c i)), ∥(f.apply) x∥ = ∥x∥)
  {n₁ : N (k' * c) i'}
  {n₂ : N c i''}
  {nnew₁ : N c i'}
  {m₁ : M c i'}
  {m : (M c₁ i)}
  --(hmulε₁ : ε₁ * (1 + K' * r₁ * r₂) = ε / 2)
  --(hle : (r₂ : ℝ) * ε₂ ≤ ε / 2)
--  (hn₁ : ∥res (f m) - (N.d i' i) n₁∥ ≤ K * ∥(N.d i (i + 1)) (f m)∥ + ε₁)
--  (hp₂ : ∥res (g n₁) - (P.d i'' i') (g n₂)∥ ≤ K' * ∥(P.d i' (i' + 1)) (g n₁)∥ + ε₂)
  (hnormnnew₁ : ∥nnew₁∥ ≤ r₂ * ∥g (res n₁ - ((N.d i'' i') n₂))∥)
  (hm₁ : f m₁ = res n₁ - ((N.d i'' i') n₂) - nnew₁)
  (hfm : ∥g ((N.d i' i) n₁)∥ = ∥g (res (f m) - (N.d i' i) n₁)∥) :
  ∥res m - (M.d i' i) m₁∥ ≤ (K + r₁ * r₂ * K * K') * ∥(M.d i (i + 1)) m∥ :=
begin
  refine le_iff_forall_pos_le_add.mpr _,
  intros ε hε,
  convert @norm_sub_le_mul_norm_add M N P f g k' K K' r₁ r₂ c c₁ ε
    ((1 + K' * r₁ * r₂)⁻¹ * ε / 2) _ hε i i' i'' hii' hk'
    fc₁ fc hN_adm hgnorm hfnorm n₁ n₂ nnew₁ m₁ m
    (_) --hmulε₁
    (_) -- hle
    _ --hn₁
    _ --hp₂
    hnormnnew₁ hm₁ hfm,
sorry,
rw [mul_comm, mul_div_assoc, mul_inv_cancel_left'],apply ne_of_gt,
refine add_pos_of_pos_of_nonneg zero_lt_one _,exact (K' * r₁ * r₂).coe_nonneg,

sorry,
end


#exit
import system_of_complexes.basic

universe variables u

noncomputable theory
open_locale nnreal
open category_theory opposite normed_group_hom system_of_complexes

variables (M N P : system_of_complexes.{u}) (f : M ⟶ N) (g : N ⟶ P)

/-  I (DT) extracted this lemma to speed up the proof of `weak_normed_snake_dual`. -/
lemma ε₁_pos (a : ℝ≥0) {ε ε₁ : ℝ} (hε : 0 < ε) (hmulε : ε₁ * (1 + a) = ε / 2) :
  0 < ε₁ :=
have one_add_pos : (0 : ℝ) < 1 + a := add_pos_of_pos_of_nonneg zero_lt_one (zero_le a),
calc 0 < ε / 2 / (1 + ↑a) : div_pos (half_pos hε) one_add_pos
       ... = _ : ((eq_div_iff one_add_pos.ne').mpr hmulε).symm

/-  I (DT) extracted this lemma to speed up the proof of `weak_normed_snake_dual`. -/
lemma norm_sub_le_mul_norm_add {k' K K' r₁ r₂ c c₁ : ℝ≥0} {ε ε₁ ε₂ : ℝ} (hε : 0 < ε)
  {i i' i'' : ℕ} (hii' : i' + 1 = i)
  [hk' : fact (1 ≤ k')]
  [fc₁ : fact (k' * c ≤ c₁)]
  [fc : fact (c ≤ c₁)]
  (hN_adm : N.admissible)
  (hgnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (N c i)), ∥g x∥ ≤ ↑r₁ * ∥x∥)
  (hfnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (M c i)), ∥(f.apply) x∥ = ∥x∥)
  {n₁ : N (k' * c) i'}
  {n₂ : N c i''}
  {nnew₁ : N c i'}
  {m₁ : M c i'}
  {m : (M c₁ i)}
  (hmulε₁ : ε₁ * (1 + K' * r₁ * r₂) = ε / 2)
  (hle : (r₂ : ℝ) * ε₂ ≤ ε / 2)
  (hn₁ : ∥res (f m) - (N.d i' i) n₁∥ ≤ K * ∥(N.d i (i + 1)) (f m)∥ + ε₁)
  (hp₂ : ∥res (g n₁) - (P.d i'' i') (g n₂)∥ ≤ K' * ∥(P.d i' (i' + 1)) (g n₁)∥ + ε₂)
  (hnormnnew₁ : ∥nnew₁∥ ≤ r₂ * ∥g (res n₁ - ((N.d i'' i') n₂))∥)
  (hm₁ : f m₁ = res n₁ - ((N.d i'' i') n₂) - nnew₁)
  (hfm : ∥g ((N.d i' i) n₁)∥ = ∥g (res (f m) - (N.d i' i) n₁)∥) :
  ∥res m - (M.d i' i) m₁∥ ≤ (K + r₁ * r₂ * K * K') * ∥(M.d i (i + 1)) m∥ + ε :=
have hε₁ : 0 < ε₁ := ε₁_pos (K' * r₁ * r₂) hε hmulε₁,
calc ∥res m - (M.d i' i) m₁∥ = ∥f (res m - (M.d i' i) m₁)∥ : (hfnorm _ _ _).symm
  ... = ∥res _ - (N.d i' i (res n₁) - N.d i' i (_ + nnew₁))∥ :
    by rw [hom_apply, normed_group_hom.map_sub, ←hom_apply, ←hom_apply, ←res_apply,
    ←d_apply, hm₁, sub_sub, normed_group_hom.map_sub]
  ... = ∥(res _ - N.d i' i (res n₁)) + N.d i' i (_ + nnew₁)∥ : by abel
  ... ≤ ∥res _ - N.d i' i _∥ + ∥N.d i' i (_ + nnew₁)∥ : norm_add_le _ _
  ... = ∥res _ - N.d i' i _∥ + ∥N.d i' i nnew₁∥ : by simp only [map_add, zero_add, d_d]
  ... ≤ ∥res _ - N.d i' i _∥ + r₂ * ∥g (res n₁ - _)∥ :
    add_le_add_left (le_trans (hN_adm.d_norm_noninc _ _ i' i nnew₁) hnormnnew₁) _
  ... = ∥res _ - N.d i' i _∥ + r₂ * ∥res _ - P.d i'' i' (g n₂)∥ :
    by rw [hom_apply g, normed_group_hom.map_sub, ←hom_apply, ←hom_apply,
    ←res_apply _ _ g, ←d_apply]
  ... ≤ ∥res _ - N.d i' i _∥ + r₂ * (K' * ∥P.d i' (i'+1) _∥ + ε₂) :
  add_le_add_left (mul_le_mul_of_nonneg_left hp₂ r₂.coe_nonneg) _
  ... = _ + r₂ * (K' * ∥P.d i' (i'+1) _∥ + ε₂) :
    by rw [←res_res, d_res, normed_group_hom.map_sub]
  ... ≤ K * _ + ε₁ + r₂ * (K' * ∥P.d i' (i'+1) _∥ + ε₂) :
  add_le_add_right (le_trans (hN_adm.res_norm_noninc _ _ _ _ _) hn₁) _
  ... = K * _ + ε₁ + r₂ * (K' * ∥g (res (f m) - N.d i' i n₁)∥ + ε₂) :
    by rw [d_apply _ _ g _, hii', hfm]
  ... ≤ K * _ + ε₁ + r₂ * (K' * (r₁ * ∥res (f m) - N.d i' i n₁∥) + ε₂) :
    add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left
      (hgnorm _ _ _) K'.coe_nonneg) _) $ r₂.coe_nonneg) _
  ... = K * _ + ε₁ + r₂ * (K' * r₁ * ∥res _ - N.d i' i n₁∥ + ε₂) : by rw mul_assoc
  ... ≤ K * _ + ε₁ + r₂ * (K' * r₁ * (K * ∥(N.d i (i+1)) _∥ + ε₁) + ε₂) :
    add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left
    hn₁ $ mul_nonneg K'.coe_nonneg r₁.coe_nonneg) _) r₂.coe_nonneg) _
  ... = (K + r₁ * r₂ * K * K') * ∥N.d i (i+1) (f m)∥ + ε₁ * (1 + K' * r₁ * r₂) + r₂ * ε₂ : by ring
  ... = (K + r₁ * r₂ * K * K') * ∥N.d i (i+1) (f m)∥ + ε / 2 + r₂ * ε₂ : by rw [hmulε₁]
  ... ≤ _ * ∥N.d i (i+1) (f m)∥ + ε / 2 + ε / 2 : add_le_add_left hle _
  ... = _ * ∥(M.d i (i+1)) m∥ + ε : by rw [add_assoc, add_halves', d_apply, hom_apply, hfnorm]


/-  I (DT) extracted this lemma to speed up the proof of `weak_normed_snake_dual`.
The `ρ` in this lemma stands for `K + r₁ * r₂ * K * K'` in the application.
 -/
lemma exists_norm_sub_le_mul_add {M : system_of_complexes} {k k' c ρ : ℝ≥0}
  {i : ℕ}
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')]
  (hM_adm : M.admissible)
  (ex_le : (∀ (m : (M (k * (k' * c)) i)) (ε : ℝ), 0 < ε →
        (∃ (i₀ : ℕ) (hi₀ : i₀ = i - 1) (y : (M c i₀)),
           ∥res m - (M.d i₀ i) y∥ ≤ ↑ρ * ∥(M.d i (i + 1)) m∥ + ε)))
  (m₁ : (M (k * k' * c) i))
  {ε : ℝ}
  (hε : 0 < ε) :
  ∃ (i₀ j : ℕ) (hi₀ : i₀ = i - 1) (hj : i + 1 = j) (y : (M c i₀)),
      ∥res m₁ - (M.d i₀ i) y∥ ≤ ↑ρ * ∥(M.d i j) m₁∥ + ε :=
begin
  haveI : fact (k * (k' * c) ≤ k * k' * c) := { out := (mul_assoc _ _ _).symm.le },
  rcases ex_le (res m₁) ε hε with ⟨i₀, rfl, y, hy⟩,
  rw [res_res, d_res] at hy,
  refine ⟨i - 1, _, rfl, rfl, _⟩,
  refine ⟨y, hy.trans (add_le_add_right (mul_le_mul_of_nonneg_left _ ρ.2) ε)⟩,
  exact hM_adm.res_norm_noninc _ _ _ _ _,
end


/-  I (DT) extracted this lemma to speed up the proof of `weak_normed_snake_dual`. -/
lemma norm_sub_le_mul_mul_norm_add {M N : system_of_complexes} {f : M ⟶ N}
  {k k' K c : ℝ≥0} (mK : ℝ≥0) {ε ε₁ : ℝ} {m : M (k * (k' * c)) 0} {n₁ : N (k' * c) 0} {m₁ : M c 0}
  (ee1 : ε₁ ≤ ε)
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')]
  (hfnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (M c i)), ∥(f.apply) x∥ = ∥x∥)
  (inadm : ∥((res (res m : (M (k' * c) 0))) : (M c 0))∥ ≤ ∥(res m : (M (k' * c) 0))∥ )
  (hn₁ : ∥res (f m) - (N.d 0 0) n₁∥ ≤ ↑K * ∥(N.d 0 (0 + 1)) (f m)∥ + ε₁) :
  ∥res m - (M.d 0 0) m₁∥ ≤ (K * (1 + mK)) * ∥(M.d 0 (0 + 1)) m∥ + ε :=
begin
  simp only [d_self_apply, sub_zero, nnreal.coe_add, nnreal.coe_mul] at hn₁ ⊢,
  rw [res_apply, hom_apply f (res m), hfnorm] at hn₁,
  have new : fact (c ≤ k' * c) := { out := le_mul_of_one_le_left c.2 hk'.out },
  rw ←res_res _ _ _ new,
  refine le_trans inadm (le_trans hn₁ _),
  rw [d_apply, hom_apply f _, hfnorm],
  refine add_le_add _ ee1,
  rw mul_assoc,
  refine (mul_le_mul_of_nonneg_left _ K.2),
  exact le_mul_of_one_le_left (norm_nonneg _) (le_add_of_nonneg_right mK.2),
end

/-  I (DT) extracted this lemma to speed up the proof of `weak_normed_snake_dual`. -/
lemma ε₁_le_ε {ε ε₁ : ℝ} (hε : 0 < ε) (mK : ℝ≥0) (hε₁ : ε₁ = ε / 2 * (1 + mK)⁻¹) :
  ε₁ ≤ ε :=
begin
  rw [hε₁, div_eq_mul_inv, mul_assoc, ← mul_inv'],
  refine mul_le_of_le_one_right (le_of_lt hε) _,
  rw mul_inv',
  refine mul_le_one nnreal.two_inv_lt_one.le (inv_nonneg.mpr (add_nonneg zero_le_one _)) _,
  { exact mK.coe_nonneg },
  { exact inv_le_one (le_add_of_nonneg_right mK.coe_nonneg) }
end

lemma weak_normed_snake_dual (k k' K K' r₁ r₂ : ℝ≥0)
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')]
  {a : ℕ} {c₀ : ℝ≥0}
  (hN : N.is_weak_bounded_exact k K (a + 1) c₀)
  (hP : P.is_weak_bounded_exact k' K' (a + 1) c₀)
  (hN_adm : N.admissible)
  (hgnrm : ∀ c i (x : N c i), ∥g x∥ ≤ r₁ * ∥x∥)
  (Hg : ∀ (c : ℝ≥0) [fact (c₀ ≤ c)] (i : ℕ) (hi : i ≤ a + 1 + 1) (y : P c i),
    ∃ (x : N c i), g x = y ∧ ∥x∥ ≤ r₂ * ∥y∥)
  (hg : ∀ c i, (f.apply : M c i ⟶ N c i).range = g.apply.ker)
  (hf : ∀ c i, @isometry (M c i) (N c i) _ _ f.apply) :
  M.is_weak_bounded_exact (k * k') (K + r₁ * r₂ * K * K') a c₀ :=
begin
  introsI c hc i hi,
  apply exists_norm_sub_le_mul_add (admissible_of_isometry hN_adm hf),
  intros m ε hε,

  have hlt : 0 < (1 + K' * r₁ * r₂ : ℝ) :=
    add_pos_of_pos_of_nonneg zero_lt_one ((K' * r₁ * r₂).coe_nonneg),
  have hε₁ : 0 < ε / 2 * (1 + K' * r₁ * r₂)⁻¹ := mul_pos (half_pos hε) (inv_pos.2 hlt),
  obtain ⟨_, _, rfl, rfl, n₁, hn₁⟩ :=
    hN _ ⟨hc.out.trans $ le_mul_of_one_le_left' hk'.out⟩ _ (trans hi a.le_succ) (f m) _ hε₁,
  have Hi' : i - 1 ≤ a + 1 := trans i.pred_le (trans hi a.le_succ),
  obtain ⟨_, _, rfl, rfl, p₂, hp₂⟩ := hP _ hc _ Hi' (g n₁)
    (if (r₂ : ℝ) = 0 then 1 else (ε / 2) * r₂⁻¹) _,
  { have Hi'' : (i - 1 - 1) ≤ a + 1 + 1 := trans (nat.pred_le _) (trans Hi' (nat.le_succ _)),
    obtain ⟨n₂, rfl, hnormn₂⟩ := Hg c (i - 1 - 1) Hi'' p₂,
    let n₁' := N.d (i - 1 - 1) (i - 1) n₂,
    obtain ⟨nnew₁, hnnew₁, hnrmnew₁⟩ := Hg c (i - 1) (trans Hi' a.succ.le_succ) (g (res n₁ - n₁')),
    have hker : (res n₁ - n₁') - nnew₁ ∈ g.apply.ker,
    { rw [mem_ker, normed_group_hom.map_sub, sub_eq_zero, ←hom_apply, ←hom_apply, hnnew₁] },
    rw ←hg at hker,
    obtain ⟨m₁, hm₁ : f m₁ = res n₁ - n₁' - nnew₁⟩ := (mem_range _ _).1 hker,
    refine ⟨i - 1, rfl, m₁, _⟩,

    have hfnrm : ∀ c i (x : M c i), ∥f.apply x∥ = ∥x∥ :=
      λ c i x, (isometry_iff_norm _).1 (hf c i) x,
    by_cases hizero : i = 0,
    { subst hizero,
      convert norm_sub_le_mul_mul_norm_add (K' * r₁ * r₂) _ hfnrm _ hn₁,
      { norm_cast, ring },
      { exact ε₁_le_ε hε (K' * r₁ * r₂) rfl },
      { exact (admissible_of_isometry hN_adm hf).res_norm_noninc _ _ _ _ _ } },

    { refine norm_sub_le_mul_norm_add M N P f g hε _ hN_adm hgnrm hfnrm _ _ hn₁ hp₂ hnrmnew₁ hm₁ _,
      { exact nat.succ_pred_eq_of_pos (nat.pos_of_ne_zero hizero) },
      { field_simp [hlt.ne.symm], ring },
      { by_cases H : r₂ = 0,
        { simp only [H, nnreal.coe_zero, if_true, zero_mul, (half_pos hε).le], },
        { simp only [H, nnreal.coe_eq_zero, if_false, mul_comm,
            mul_inv_cancel_left' (nnreal.coe_ne_zero.mpr H)] } },
      { have : f (res m : M (k' * c) i) ∈ f.apply.range, { rw mem_range, exact ⟨res m, rfl⟩ },
        rw [hg, mem_ker] at this,
        rw [hom_apply g (res (f m) - (N.d (i - 1) i) n₁), res_apply, normed_group_hom.map_sub, this,
          zero_sub, norm_neg, ←hom_apply] } } },
  { by_cases H : r₂ = 0,
    { simp only [H, zero_lt_one, if_true, eq_self_iff_true, nnreal.coe_eq_zero] },
    { simp only [H, nnreal.coe_eq_zero, if_false],
      exact mul_pos (half_pos hε) (inv_pos.2 (nnreal.coe_pos.2 (zero_lt_iff.2 H))) } }
end








#exit
/- Attempt at reordering K K'. -/
lemma ggexample (M N : system_of_complexes) {k k' K mK c : ℝ≥0}
  {ε ε₁ : ℝ}
  (f : M ⟶ N)
  [hk : fact (1 ≤ k)]
  [hk' : fact (1 ≤ k')]
  (hfnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (M c i)), ∥(f.apply) x∥ = ∥x∥)
  (hε : 0 < ε)
  (hlt : (0 : ℝ) < 1 + mK)
  (hmulε₁ : ε₁ * (1 + mK) * 2 = ε)
  {m : M (k * (k' * c)) 0}
  (inadm : ∥((res (res m : (M (k' * c) 0))) : (M c 0))∥ ≤ ∥(res m : (M (k' * c) 0))∥ )
  {n₁ : N (k' * c) 0}
  {m₁ : M c 0}
  (hn₁ : ∥res (f m) - (N.d 0 0) n₁∥ ≤ ↑K * ∥(N.d 0 (0 + 1)) (f m)∥ + ε₁) :
  ∥res m - (M.d 0 0) m₁∥ ≤ (K * (1 + mK)) * ∥(M.d 0 (0 + 1)) m∥ + ε :=
begin
  simp only [d_self_apply, sub_zero, nnreal.coe_add, nnreal.coe_mul] at hn₁ ⊢,
  rw [res_apply, hom_apply f (res m), hfnorm] at hn₁,
  have new : fact (c ≤ k' * c) := { out := le_mul_of_one_le_left c.2 hk'.out },
  rw ←res_res _ _ _ new,
  refine le_trans inadm (le_trans hn₁ _),
  rw [d_apply, hom_apply f _, hfnorm],
  refine add_le_add _ _,
  { rw mul_assoc,
    refine (mul_le_mul_of_nonneg_left _ K.2),
    exact le_mul_of_one_le_left (norm_nonneg _) (le_add_of_nonneg_right mK.2) },
  { rw [← hmulε₁, mul_assoc],
    refine le_mul_of_one_le_right (le_of_lt _) _,
    { rwa [← hmulε₁, mul_assoc, ← div_lt_iff _, zero_div] at hε,
      exact mul_pos (add_pos_of_pos_of_nonneg zero_lt_one mK.2) zero_lt_two },
    { exact trans (le_add_of_nonneg_right mK.2) ((le_mul_iff_one_le_right hlt).mpr one_le_two) } }
end
#lint

#exit
/- Trying with i'=0. -/
lemma ggexample (M N : system_of_complexes) {k k' K K' r₁ r₂ c : ℝ≥0}
  {ε ε₁ : ℝ}
  (f : M ⟶ N)
  [hk : fact (1 ≤ k)]
  [hk' : fact (1 ≤ k')]
  (hfnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (M c i)), ∥(f.apply) x∥ = ∥x∥)
  (hε : 0 < ε)
  (hlt : (0 : ℝ) < 1 + K' * r₁ * r₂)
  (hmulε₁ : ε₁ * (1 + ↑K' * ↑r₁ * ↑r₂) = ε / 2)
  {m : M (k * (k' * c)) 0}
  (inadm : ∥((res (res m : (M (k' * c) 0))) : (M c 0))∥ ≤ ∥(res m : (M (k' * c) 0))∥ )
  {n₁ : N (k' * c) 0}
  {m₁ : M c 0}
  (hn₁ : ∥res (f m) - (N.d 0 0) n₁∥ ≤ ↑K * ∥(N.d 0 (0 + 1)) (f m)∥ + ε₁) :
  ∥res m - (M.d 0 0) m₁∥ ≤
    (↑K + ↑r₁ * ↑r₂ * ↑K * ↑K') * ∥(M.d 0 (0 + 1)) m∥ +
      ε :=
begin
  simp only [d_self_apply, sub_zero, nnreal.coe_add, nnreal.coe_mul] at hn₁ ⊢,
  rw [res_apply, hom_apply f (res m), hfnorm] at hn₁,
  have new : fact (c ≤ k' * c) := { out := le_mul_of_one_le_left c.2 hk'.out },
  rw ←res_res _ _ _ new,
  refine le_trans inadm (le_trans hn₁ _),
--  refine le_trans (hM_adm.res_norm_noninc _ _ _ _ _) (le_trans hn₁ _),
  have : (↑K + ↑r₁ * ↑r₂ * ↑K * ↑K') * ∥M.d 0 1 m∥ + ε =
    ↑K * ∥M.d 0 1 m∥ + (↑r₁ * ↑r₂ * ↑K * ↑K' * ∥M.d 0 1 m∥ + ε) := by ring,
  rw [d_apply, hom_apply f _, hfnorm, this],
  have hmul : (↑r₁ * ↑r₂ * ↑K * ↑K' * ∥M.d 0 1 m∥ + (ε / 2 + ε / 2)) * (1 + ↑K' * ↑r₁ * ↑r₂) =
    (ε / 2) + ((ε / 2) + (↑r₁ * ↑r₂ * ↑K * ↑K' * ∥M.d 0 1 m∥ +
    ↑r₁ * ↑r₂ * ↑K * ↑K' * ∥M.d 0 1 m∥ * ↑K' * ↑r₁ * ↑r₂ +
    ε * (↑K' * ↑r₁ * ↑r₂))) := by ring,
  refine add_le_add_left ((mul_le_mul_right hlt).1 _) _,
  rw [←add_halves' ε, hmulε₁, hmul, ←coe_nnnorm],
  exact_mod_cast (le_add_iff_nonneg_right (ε / 2)).2 (add_nonneg (half_pos hε).le
    (add_nonneg (nnreal.coe_nonneg _) (mul_nonneg (gt.lt hε).le (nnreal.coe_nonneg _)))),
end
#lint

#exit
/- Works! -/
lemma ggexample (M N : system_of_complexes) (k k' K K' r₁ r₂ : ℝ≥0) {a : ℕ}
   (c : ℝ≥0) (ε : ℝ) (i' i'' : ℕ)
  (f : M ⟶ N)
  [hk : fact (1 ≤ k)]
  [hk' : fact (1 ≤ k')]
  (hfnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (M c i)), ∥(f.apply) x∥ = ∥x∥)
  (hM_adm : M.admissible)
  (hε : ε > 0)
  (hlt : (0 : ℝ) < 1 + K' * r₁ * r₂)
  (n₁ : (N (k' * c) i'))
  (Hi' : i' ≤ a + 1)
  (hi'' : i'' = i' - 1)
  (nnew₁ : (N c i'))
  (m₁ : (M c i'))
  (hi' : i' = 0 - 1)
  {ε₁ : ℝ}
  (hmulε₁ : ε₁ * (1 + K' * r₁ * r₂) = ε / 2)
  (m : (M (k * (k' * c)) 0))
  (hn₁ : ∥res (f m) - (N.d i' 0) n₁∥ ≤ K * ∥(N.d 0 (0 + 1)) (f m)∥ + ε₁) :
  ∥res m - (M.d i' 0) m₁∥ ≤ (K + r₁ * r₂ * K * K') * ∥(M.d 0 (0 + 1)) m∥ + ε :=
begin
  rw [nat.zero_sub] at hi',
  subst hi',
  simp only [d_self_apply, sub_zero, nnreal.coe_add, nnreal.coe_mul] at hn₁ ⊢,
  rw [res_apply, hom_apply f (res m), hfnorm] at hn₁,
  rw ←@res_res _ _ (k' * c) c _ _ _ _,
  refine le_trans (hM_adm.res_norm_noninc _ _ _ _ _) (le_trans hn₁ _),
  have : (↑K + ↑r₁ * ↑r₂ * ↑K * ↑K') * ∥M.d 0 1 m∥ + ε =
    ↑K * ∥M.d 0 1 m∥ + (↑r₁ * ↑r₂ * ↑K * ↑K' * ∥M.d 0 1 m∥ + ε) := by ring,
  rw [d_apply, hom_apply f _, hfnorm, this],
  have hmul : (↑r₁ * ↑r₂ * ↑K * ↑K' * ∥M.d 0 1 m∥ + (ε / 2 + ε / 2)) * (1 + ↑K' * ↑r₁ * ↑r₂) =
    (ε / 2) + ((ε / 2) + (↑r₁ * ↑r₂ * ↑K * ↑K' * ∥M.d 0 1 m∥ +
    ↑r₁ * ↑r₂ * ↑K * ↑K' * ∥M.d 0 1 m∥ * ↑K' * ↑r₁ * ↑r₂ +
    ε * (↑K' * ↑r₁ * ↑r₂))) := by ring,
  refine add_le_add_left ((mul_le_mul_right hlt).1 _) _,
  rw [←add_halves' ε, hmulε₁, hmul, ←coe_nnnorm],
  exact_mod_cast (le_add_iff_nonneg_right (ε / 2)).2 (add_nonneg (half_pos hε).le
    (add_nonneg (nnreal.coe_nonneg _) (mul_nonneg (gt.lt hε).le (nnreal.coe_nonneg _)))),
end
#lint

#exit





lemma weak_normed_snake_dual (k k' K K' r₁ r₂ c₀: ℝ≥0) {a : ℕ}
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')]
  (hN : N.is_weak_bounded_exact k K (a + 1) c₀)
  (hP : P.is_weak_bounded_exact k' K' (a + 1) c₀)
  (hN_adm : N.admissible)
  (hgnorm : ∀ c i (x : N c i), ∥g x∥ ≤ r₁ * ∥x∥)
  (Hg : ∀ (c : ℝ≥0) [fact (c₀ ≤ c)] (i : ℕ) (hi : i ≤ a + 1 + 1) (y : P c i),
    ∃ (x : N c i), g x = y ∧ ∥x∥ ≤ r₂ * ∥y∥)
  (hg : ∀ c i, (f.apply : M c i ⟶ N c i).range = g.apply.ker)
  (hf : ∀ c i, @isometry (M c i) (N c i) _ _ f.apply) :
  M.is_weak_bounded_exact (k * k') (K + r₁ * r₂ * K * K') a c₀ :=
begin
  introsI c hc i hi,
  have hM_adm : M.admissible := admissible_of_isometry hN_adm hf,
  intros m ε hε,
  apply anequivexample M hM_adm _ _ hε,
  set ε₁ := ε / 2 * (1 + K' * r₁ * r₂)⁻¹ with iε₁,
  have hlt : 0 < (1 + K' * r₁ * r₂ : ℝ),
  { refine add_pos_of_pos_of_nonneg zero_lt_one _,
    rw [←nnreal.coe_mul, ←nnreal.coe_mul],
    exact nnreal.coe_nonneg _ },
  have hε₁ : 0 < ε₁ := mul_pos (half_pos hε) (inv_pos.2 hlt),
  let ε₂ := if (r₂ : ℝ) = 0 then 1 else (ε / 2) * r₂⁻¹,
  have hle : ↑r₂ * ε₂ ≤ ε / 2,
  { by_cases H : r₂ = 0,
    { simp only [H, nnreal.coe_zero, zero_mul, (half_pos hε).le], },
    { simp only [H, nnreal.coe_eq_zero, if_false, mul_ite],
      rw [mul_comm, mul_assoc, inv_mul_cancel (by rwa ← nnreal.coe_eq_zero at H), mul_one] } },
  have hε₂ : 0 < ε₂,
  { --change 0 < (if (r₂ : ℝ) = 0 then 1 else (ε / 2) * r₂⁻¹),
    by_cases H : r₂ = 0,
    { simp only [ε₂, H, zero_lt_one, if_true, eq_self_iff_true, nnreal.coe_eq_zero] },
    { simp only [ε₂, H, nnreal.coe_eq_zero, if_false],
      exact mul_pos (half_pos hε) (inv_pos.2 (nnreal.coe_pos.2 (zero_lt_iff.2 H))) } },
  obtain ⟨_, _, rfl, rfl, n₁, hn₁⟩ :=
    hN _ ⟨hc.out.trans $ le_mul_of_one_le_left' hk'.out⟩ _ (trans hi a.le_succ) (by {
      rw ← mul_assoc,exact f m }) ε₁ hε₁,
  have Hi' : i - 1 ≤ a + 1 := trans i.pred_le (trans hi a.le_succ),
  obtain ⟨_, _, rfl, rfl, p₂, hp₂⟩ := hP _ hc _ Hi' (g n₁) ε₂ hε₂,
  have Hi'' : (i - 1 - 1) ≤ a + 1 + 1 := trans ((i - 1).pred_le) (trans Hi' (nat.le_succ _)),
  obtain ⟨n₂, rfl, hnormn₂⟩ := Hg c (i - 1 - 1) Hi'' p₂,
  set n₁' := N.d (i - 1 - 1) (i - 1) n₂ with hdefn₁',
  obtain ⟨nnew₁, hnnew₁, hnormnnew₁⟩ := Hg c (i - 1) (le_trans Hi' (nat.le_succ _)) (g (res n₁ - n₁')),
  have hker : (res n₁ - n₁') - nnew₁ ∈ g.apply.ker,
  { rw [mem_ker, normed_group_hom.map_sub, sub_eq_zero, ←hom_apply, ←hom_apply, hnnew₁] },
  rw ←hg at hker,
  obtain ⟨m₁, hm₁ : f m₁ = res n₁ - n₁' - nnew₁⟩ := (mem_range _ _).1 hker,
  intros m3 ε3 hε3,
  refine ⟨i - 1, rfl, m₁, _⟩,
  have hfnorm : ∀ c i (x : M c i), ∥f.apply x∥ = ∥x∥ :=
    λ c i x, (isometry_iff_norm _).1 (hf c i) x,
  have hmulε₁ : ε₁ *  (1 + K' * r₁ * r₂) = ε / 2 :=
    ((mul_inv_eq_iff_eq_mul' hlt.ne').mp iε₁.symm).symm,
  by_cases hizero : i = 0,
  { subst hizero,
    simp only [d_self_apply, sub_zero, nnreal.coe_add, nnreal.coe_mul] at hn₁ ⊢,
    sorry,
    rw [res_apply, hom_apply f (res m), hfnorm] at hn₁,
    rw ←@res_res _ _ (k' * c) c _ _ _ _,
    refine le_trans (hM_adm.res_norm_noninc _ _ _ _ _) (le_trans hn₁ _),
    have : (↑K + ↑r₁ * ↑r₂ * ↑K * ↑K') * ∥M.d 0 1 m∥ + ε =
      ↑K * ∥M.d 0 1 m∥ + (↑r₁ * ↑r₂ * ↑K * ↑K' * ∥M.d 0 1 m∥ + ε) := by ring,
    rw [d_apply, hom_apply f _, hfnorm, this],
    refine add_le_add_left ((mul_le_mul_right hlt).1 _) _,
    have hmul : (↑r₁ * ↑r₂ * ↑K * ↑K' * ∥M.d 0 1 m∥ + (ε / 2 + ε / 2)) * (1 + ↑K' * ↑r₁ * ↑r₂) =
      (ε / 2) + ((ε / 2) + (↑r₁ * ↑r₂ * ↑K * ↑K' * ∥M.d 0 1 m∥ +
      ↑r₁ * ↑r₂ * ↑K * ↑K' * ∥M.d 0 1 m∥ * ↑K' * ↑r₁ * ↑r₂ +
      ε * (↑K' * ↑r₁ * ↑r₂))) := by ring,
    rw [←add_halves' ε, hmulε₁, hmul, ←coe_nnnorm],
    exact_mod_cast (le_add_iff_nonneg_right (ε / 2)).2 (add_nonneg (half_pos hε).le
      (add_nonneg (nnreal.coe_nonneg _) (mul_nonneg (gt.lt hε).le (nnreal.coe_nonneg _)))) },
  have hfm : ∥g (N.d (i - 1) i n₁)∥ = ∥g (res (f m) - N.d (i - 1) i n₁)∥,
  { have : f (@res _ _ (k' * c) _ _ m) ∈ f.apply.range := by { rw mem_range, exact ⟨res m, rfl⟩ },
    rw [hg, mem_ker] at this,
    rw [hom_apply g (res (f m) - (N.d (i - 1) i) n₁), res_apply, normed_group_hom.map_sub, this,
      zero_sub, norm_neg, ←hom_apply] },
  refine fexample M N P f g hε (nat.sub_add_cancel (nat.pos_of_ne_zero hizero)) hN_adm hgnorm hfnorm
    hmulε₁ hle hn₁ hp₂ hnormnnew₁ hm₁ hfm,
end


#exit

/-  prima di un rfl -/
lemma weak_normed_snake_dual (k k' K K' r₁ r₂ c₀: ℝ≥0) {a : ℕ}
  [hk : fact (1 ≤ k)] [hk' : fact (1 ≤ k')]
  (hN : N.is_weak_bounded_exact k K (a + 1) c₀)
  (hP : P.is_weak_bounded_exact k' K' (a + 1) c₀)
  (hN_adm : N.admissible)
  (hgnorm : ∀ c i (x : N c i), ∥g x∥ ≤ r₁ * ∥x∥)
  (Hg : ∀ (c : ℝ≥0) [fact (c₀ ≤ c)] (i : ℕ) (hi : i ≤ a + 1 + 1) (y : P c i),
    ∃ (x : N c i), g x = y ∧ ∥x∥ ≤ r₂ * ∥y∥)
  (hg : ∀ c i, (f.apply : M c i ⟶ N c i).range = g.apply.ker)
  (hf : ∀ c i, @isometry (M c i) (N c i) _ _ f.apply) :
  M.is_weak_bounded_exact (k * k') (K + r₁ * r₂ * K * K') a c₀ :=
begin
  introsI c hc i hi,
  have hM_adm : M.admissible := admissible_of_isometry hN_adm hf,
  apply anequivexample M _ hM_adm,
  intros m ε hε,
  set ε₁ := ε / 2 * (1 + K' * r₁ * r₂)⁻¹ with iε₁,
  have hlt : 0 < (1 + K' * r₁ * r₂ : ℝ),
  { refine add_pos_of_pos_of_nonneg zero_lt_one _,
    rw [←nnreal.coe_mul, ←nnreal.coe_mul],
    exact nnreal.coe_nonneg _ },
  have hε₁ : 0 < ε₁ := mul_pos (half_pos hε) (inv_pos.2 hlt),
  let ε₂ := if (r₂ : ℝ) = 0 then 1 else (ε / 2) * r₂⁻¹,
  have hle : ↑r₂ * ε₂ ≤ ε / 2,
  { by_cases H : r₂ = 0,
    { simp only [H, nnreal.coe_zero, zero_mul, (half_pos hε).le], },
    { simp only [H, nnreal.coe_eq_zero, if_false, mul_ite],
      rw [mul_comm, mul_assoc, ←nnreal.coe_inv, ←nnreal.coe_mul, inv_mul_cancel H,
        nnreal.coe_one, mul_one] } },
  have hε₂ : 0 < ε₂,
  { change 0 < (if (r₂ : ℝ) = 0 then 1 else (ε / 2) * r₂⁻¹),
    by_cases H : r₂ = 0,
    { simp only [H, zero_lt_one, if_true, eq_self_iff_true, nnreal.coe_eq_zero] },
    { simp only [H, nnreal.coe_eq_zero, if_false],
      exact mul_pos (half_pos hε) (inv_pos.2 (nnreal.coe_pos.2 (zero_lt_iff.2 H))) } },
  obtain ⟨i', j', hi', rfl, n₁, hn₁⟩ :=
    hN _ ⟨hc.out.trans $ le_mul_of_one_le_left' hk'.out⟩ _ (trans hi a.le_succ) (f m) ε₁ hε₁,
  set p₁ := g n₁ with hdefp₁,
  have Hi' : i' ≤ a + 1,
  { rw [hi', nat.sub_one], exact le_trans i.pred_le (trans hi a.le_succ) },
  obtain ⟨i'', j'', hi'', rfl, p₂, hp₂⟩ := hP _ hc _ Hi' p₁ ε₂ hε₂,
  have Hi'' : i'' ≤ a + 1 + 1,
  { rw [hi'', hi', nat.sub_one, nat.sub_one],
    refine le_trans (nat.pred_le _) (le_trans (nat.pred_le _) _),
    exact trans hi (nat.le_succ_of_le a.le_succ) },
  obtain ⟨n₂, hn₂, hnormn₂⟩ := Hg c i'' Hi'' p₂,
  set n₁' := N.d i'' i' n₂ with hdefn₁',
  obtain ⟨nnew₁, hnnew₁, hnormnnew₁⟩ := Hg c i' (le_trans Hi' (nat.le_succ _)) (g (res n₁ - n₁')),
  have hker : (res n₁ - n₁') - nnew₁ ∈ g.apply.ker,
  { rw [mem_ker, normed_group_hom.map_sub, sub_eq_zero, ←hom_apply, ←hom_apply, hnnew₁] },
  rw ←hg at hker,
  obtain ⟨m₁, hm₁ : f m₁ = res n₁ - n₁' - nnew₁⟩ := (mem_range _ _).1 hker,
  refine ⟨i', hi', m₁, _⟩,
  have hfnorm : ∀ c i (x : M c i), ∥f.apply x∥ = ∥x∥ :=
    λ c i x, (isometry_iff_norm _).1 (hf c i) x,
  have hmulε₁ : ε₁ *  (1 + K' * r₁ * r₂) = ε / 2 :=
    ((mul_inv_eq_iff_eq_mul' hlt.ne').mp iε₁.symm).symm,
  by_cases hizero : i = 0,
  { subst hizero,
    rw [nat.zero_sub] at hi',
    subst hi',
    simp only [d_self_apply, sub_zero, nnreal.coe_add, nnreal.coe_mul] at hn₁ ⊢,
    rw [res_apply, hom_apply f (res m), hfnorm] at hn₁,
    rw ←@res_res _ _ (k' * c) c _ _ _ _,
    refine le_trans (hM_adm.res_norm_noninc _ _ _ _ _) (le_trans hn₁ _),
    have : (↑K + ↑r₁ * ↑r₂ * ↑K * ↑K') * ∥M.d 0 1 m∥ + ε =
      ↑K * ∥M.d 0 1 m∥ + (↑r₁ * ↑r₂ * ↑K * ↑K' * ∥M.d 0 1 m∥ + ε) := by ring,
    rw [d_apply, hom_apply f _, hfnorm, this],
    refine add_le_add_left ((mul_le_mul_right hlt).1 _) _,
    have hmul : (↑r₁ * ↑r₂ * ↑K * ↑K' * ∥M.d 0 1 m∥ + (ε / 2 + ε / 2)) * (1 + ↑K' * ↑r₁ * ↑r₂) =
      (ε / 2) + ((ε / 2) + (↑r₁ * ↑r₂ * ↑K * ↑K' * ∥M.d 0 1 m∥ +
      ↑r₁ * ↑r₂ * ↑K * ↑K' * ∥M.d 0 1 m∥ * ↑K' * ↑r₁ * ↑r₂ +
      ε * (↑K' * ↑r₁ * ↑r₂))) := by ring,
    rw [←add_halves' ε, hmulε₁, hmul, ←coe_nnnorm],
    exact_mod_cast (le_add_iff_nonneg_right (ε / 2)).2 (add_nonneg (half_pos hε).le
      (add_nonneg (nnreal.coe_nonneg _) (mul_nonneg (gt.lt hε).le (nnreal.coe_nonneg _)))) },
  have hii' : i'+1 = i,
  { rw [hi', nat.sub_one, nat.add_one, nat.succ_pred_eq_of_pos (zero_lt_iff.mpr hizero)] },
  have hfm : ∥g (N.d i' i n₁)∥ = ∥g (res (f m) - N.d i' i n₁)∥,
  { have : f (@res _ _ (k' * c) _ _ m) ∈ f.apply.range := by { rw mem_range, exact ⟨res m, rfl⟩ },
    rw [hg, mem_ker] at this,
    rw [hom_apply g (res (f m) - (N.d i' i) n₁), res_apply, normed_group_hom.map_sub, this,
      zero_sub, norm_neg, ←hom_apply] },
  exact fexample M N P f g k' K K' r₁ r₂ c hε i i' i'' hN_adm hgnorm hfnorm n₁ p₂ n₂
    hn₂ nnew₁ m₁ hii' m hmulε₁ hle hn₁ hp₂ hnormnnew₁ hm₁ hfm,
end



#lint
#exit
/- funziona con molte costanti. -/
lemma anequivexample (M : system_of_complexes) (k k' K K' r₁ r₂ c : ℝ≥0)
  (i : ℕ)
  [hk : fact (1 ≤ k)]
  [hk' : fact (1 ≤ k')]
  (hM_adm : M.admissible)
  (hK : 0 ≤ K + r₁ * r₂ * K * K')
  (this : (∀ (m : (M (k * (k' * c)) i)) (ε : ℝ), 0 < ε →
        (∃ (i₀ : ℕ) (hi₀ : i₀ = i - 1) (y : (M c i₀)),
           ∥res m - (M.d i₀ i) y∥ ≤ ↑(K + r₁ * r₂ * K * K') * ∥(M.d i (i + 1)) m∥ + ε)))
  (m₁ : (M (k * k' * c) i))
  {ε : ℝ}
  (hε : 0 < ε) :
  ∃ (i₀ j : ℕ) (hi₀ : i₀ = i - 1) (hj : i + 1 = j) (y : (M c i₀)),
      ∥res m₁ - (M.d i₀ i) y∥ ≤ ↑(K + r₁ * r₂ * K * K') * ∥(M.d i j) m₁∥ + ε :=
begin
  haveI hc : fact (k * (k' * c) ≤ k * k' * c) := { out := (mul_assoc _ _ _).symm.le },
  rcases this (res m₁) ε hε with ⟨i₀, hi₀, y, hy⟩,
  rw [res_res, d_res] at hy,
  refine ⟨i₀, _, hi₀, rfl, _⟩,
  refine ⟨y, hy.trans (add_le_add_right (mul_le_mul_of_nonneg_left _ hK) ε)⟩,
  exact hM_adm.res_norm_noninc _ _ _ _ _,
end

#lint
#exit





/- no n₁ even more cleanups -/
lemma fexample (M N P : system_of_complexes) (k' K K' r₁ r₂ c : ℝ≥0)
  (i : ℕ) (ε : ℝ) (i' i'' : ℕ)
  (f : M ⟶ N)
  (g : N ⟶ P)
  [hk' : fact (1 ≤ k')]
  (hN_adm : N.admissible)
  (hgnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (N c i)), ∥g x∥ ≤ ↑r₁ * ∥x∥)
  (hfnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (M c i)), ∥(f.apply) x∥ = ∥x∥)
  (n₁ : N (k' * c) i')
  (p₂ : P c i'')
  (n₂ : N c i'')
  (hn₂ : g n₂ = p₂)
  (nnew₁ : N c i')
  (m₁ : M c i')
  (hii' : i' + 1 = i)
  {c₁ : ℝ≥0}
  {ε₁ ε₂ : ℝ}
  [fc₁ : fact (k' * c ≤ c₁)]
  [fc : fact (c ≤ c₁)]
  (m : (M c₁ i))
  (hmulε₁ : ε₁ * (1 + K' * r₁ * r₂) = ε / 2)
  (hle : (r₂ : ℝ) * ε₂ ≤ ε / 2)
  (hn₁ : ∥res (f m) - (N.d i' i) n₁∥ ≤ K * ∥(N.d i (i + 1)) (f m)∥ + ε₁)
  (hp₂ : ∥res (g n₁) - (P.d i'' i') p₂∥ ≤ K' * ∥(P.d i' (i' + 1)) (g n₁)∥ + ε₂) :
--    (let n₁' : (N c i') := (N.d i'' i') n₂
--     in
--      n₁' = (N.d i'' i') n₂ →
        ∥nnew₁∥ ≤ r₂ * ∥g (res n₁ - ((N.d i'' i') n₂))∥ →
        f m₁ = res n₁ - ((N.d i'' i') n₂) - nnew₁ →
        ∥g ((N.d i' i) n₁)∥ = ∥g (res (f m) - (N.d i' i) n₁)∥ →
        ∥res m - (M.d i' i) m₁∥ ≤ (K + r₁ * r₂ * K * K') * ∥(M.d i (i + 1)) m∥ + ε :=
begin
  intros --nn₁'   hdefn₁'
   hnormnnew₁ hm₁ hfm,
   have hε₁ : 0 < ε₁, sorry,
    calc ∥res m - (M.d i' i) m₁∥ = ∥f (res m - (M.d i' i) m₁)∥ : (hfnorm _ _ _).symm
    ... = ∥res _ - (N.d i' i (res n₁) - N.d i' i (_ + nnew₁))∥ :
      by rw [hom_apply, normed_group_hom.map_sub, ←hom_apply, ←hom_apply, ←res_apply,
      ←d_apply, hm₁, sub_sub, normed_group_hom.map_sub]
    ... = ∥(res _ - N.d i' i (res n₁)) + N.d i' i (_ + nnew₁)∥ : by abel
    ... ≤ ∥res _ - N.d i' i _∥ + ∥N.d i' i (_ + nnew₁)∥ : norm_add_le _ _
    ... = ∥res _ - N.d i' i _∥ + ∥N.d i' i nnew₁∥ : by simp only [map_add, zero_add, d_d]
    ... ≤ ∥res _ - N.d i' i _∥ + r₂ * ∥g (res n₁ - _)∥ :
        add_le_add_left (le_trans (hN_adm.d_norm_noninc _ _ i' i nnew₁) hnormnnew₁) _
    ... = ∥res _ - N.d i' i _∥ + r₂ * ∥res _ - P.d i'' i' p₂∥ :
      by rw [hom_apply g, normed_group_hom.map_sub, ←hom_apply, ←hom_apply,
       ←res_apply _ _ g, ←d_apply, hn₂]
    ... ≤ ∥res _ - N.d i' i _∥ + r₂ * (K' * ∥P.d i' (i'+1) _∥ + ε₂) :
      add_le_add_left (mul_le_mul_of_nonneg_left hp₂ r₂.coe_nonneg) _
    ... = _ + r₂ * (K' * ∥P.d i' (i'+1) _∥ + ε₂) :
      by rw [←res_res, d_res, normed_group_hom.map_sub]
    ... ≤ K * _ + ε₁ + r₂ * (K' * ∥P.d i' (i'+1) _∥ + ε₂) :
      add_le_add_right (le_trans (hN_adm.res_norm_noninc _ _ _ _ _) hn₁) _
    ... = K * _ + ε₁ + r₂ * (K' * ∥g (res (f m) - N.d i' i n₁)∥ + ε₂) :
      by rw [d_apply _ _ g _, hii', hfm]
    ... ≤ K * _ + ε₁ + r₂ * (K' * (r₁ * ∥res (f m) - N.d i' i n₁∥) + ε₂) :
      add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left
      (hgnorm _ _ _) K'.coe_nonneg) _) $ r₂.coe_nonneg) _
    ... = K * _ + ε₁ + r₂ * (K' * r₁ * ∥res _ - N.d i' i n₁∥ + ε₂) : by rw mul_assoc
    ... ≤ K * _ + ε₁ + r₂ * (K' * r₁ * (K * ∥(N.d i (i+1)) _∥ + ε₁) + ε₂) :
      add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left
      hn₁ $ mul_nonneg K'.coe_nonneg r₁.coe_nonneg) _) r₂.coe_nonneg) _
    ... = (K + r₁ * r₂ * K * K') * ∥N.d i (i+1) (f m)∥ + ε₁ * (1 + K' * r₁ * r₂) + r₂ * ε₂ : by ring
    ... = (K + r₁ * r₂ * K * K') * ∥N.d i (i+1) (f m)∥ + ε / 2 + r₂ * ε₂ : by simp [hmulε₁]
    ... ≤ _ * ∥N.d i (i+1) (f m)∥ + ε / 2 + ε / 2 : add_le_add_left hle _
    ... = _ * ∥(M.d i (i+1)) m∥ + ε : by rw [add_assoc, add_halves', d_apply, hom_apply, hfnorm]
end

#lint
#exit




/- no p₁ even more cleanups -/
lemma fexample (M N P : system_of_complexes) (k' K K' r₁ r₂ c : ℝ≥0)
  (i : ℕ) (ε : ℝ) (i' i'' : ℕ)
  (f : M ⟶ N)
  (g : N ⟶ P)
  [hk' : fact (1 ≤ k')]
  (hN_adm : N.admissible)
  (hgnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (N c i)), ∥g x∥ ≤ ↑r₁ * ∥x∥)
  (hfnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (M c i)), ∥(f.apply) x∥ = ∥x∥)
  (n₁ : N (k' * c) i')
  (p₂ : P c i'')
  (n₂ : N c i'')
  (hn₂ : g n₂ = p₂)
  (nnew₁ : N c i')
  (m₁ : M c i')
  (hii' : i' + 1 = i)
  {c₁ : ℝ≥0}
  {ε₁ ε₂ : ℝ}
  [fc₁ : fact (k' * c ≤ c₁)]
  [fc : fact (c ≤ c₁)]
  (m : (M c₁ i))
  (hmulε₁ : ε₁ * (1 + K' * r₁ * r₂) = ε / 2)
  (hle : (r₂ : ℝ) * ε₂ ≤ ε / 2)
  (hn₁ : ∥res (f m) - (N.d i' i) n₁∥ ≤ K * ∥(N.d i (i + 1)) (f m)∥ + ε₁) :
--    (let p₁ : (P (k' * c) i') := g n₁
--     in
--      p₁ = g n₁ →
        ∥res (g n₁) - (P.d i'' i') p₂∥ ≤ K' * ∥(P.d i' (i' + 1)) (g n₁)∥ + ε₂ →
        (let n₁' : (N c i') := (N.d i'' i') n₂
         in
          n₁' = (N.d i'' i') n₂ →
            ∥nnew₁∥ ≤ r₂ * ∥g (res n₁ - n₁')∥ →
            f m₁ = res n₁ - n₁' - nnew₁ →
            ∥g ((N.d i' i) n₁)∥ = ∥g (res (f m) - (N.d i' i) n₁)∥ →
            ∥res m - (M.d i' i) m₁∥ ≤ (K + r₁ * r₂ * K * K') * ∥(M.d i (i + 1)) m∥ + ε) :=
begin
  intros --pp₁ hdefp₁
   hp₂ n₁' hdefn₁' hnormnnew₁ hm₁ hfm,
   have hε₁ : 0 < ε₁, sorry,
    calc ∥res m - (M.d i' i) m₁∥ = ∥f (res m - (M.d i' i) m₁)∥ : (hfnorm _ _ _).symm
    ... = ∥res _ - (N.d i' i (res n₁) - N.d i' i (n₁' + nnew₁))∥ :
      by rw [hom_apply, normed_group_hom.map_sub, ←hom_apply, ←hom_apply, ←res_apply,
      ←d_apply, hm₁, sub_sub, normed_group_hom.map_sub]
    ... = ∥(res _ - N.d i' i (res n₁)) + N.d i' i (n₁' + nnew₁)∥ : by abel
    ... ≤ ∥res _ - N.d i' i _∥ + ∥N.d i' i (n₁' + nnew₁)∥ : norm_add_le _ _
    ... = ∥res _ - N.d i' i _∥ + ∥N.d i' i nnew₁∥ : by simp only [map_add, zero_add, d_d]
    ... ≤ ∥res _ - N.d i' i _∥ + r₂ * ∥g (res n₁ - n₁')∥ :
        add_le_add_left (le_trans (hN_adm.d_norm_noninc _ _ i' i nnew₁) hnormnnew₁) _
    ... = ∥res _ - N.d i' i _∥ + r₂ * ∥res _ - P.d i'' i' p₂∥ :
      by rw [hom_apply g, normed_group_hom.map_sub, ←hom_apply, ←hom_apply,
       ←res_apply _ _ g, hdefn₁', ←d_apply, hn₂]
    ... ≤ ∥res _ - N.d i' i _∥ + r₂ * (K' * ∥P.d i' (i'+1) _∥ + ε₂) :
      add_le_add_left (mul_le_mul_of_nonneg_left hp₂ r₂.coe_nonneg) _
    ... = _ + r₂ * (K' * ∥P.d i' (i'+1) _∥ + ε₂) :
      by rw [←res_res, d_res, normed_group_hom.map_sub]
    ... ≤ K * _ + ε₁ + r₂ * (K' * ∥P.d i' (i'+1) _∥ + ε₂) :
      add_le_add_right (le_trans (hN_adm.res_norm_noninc _ _ _ _ _) hn₁) _
    ... = K * _ + ε₁ + r₂ * (K' * ∥g (res (f m) - N.d i' i n₁)∥ + ε₂) :
      by rw [d_apply _ _ g _, hii', hfm]
    ... ≤ K * _ + ε₁ + r₂ * (K' * (r₁ * ∥res (f m) - N.d i' i n₁∥) + ε₂) :
      add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left
      (hgnorm _ _ _) K'.coe_nonneg) _) $ r₂.coe_nonneg) _
    ... = K * _ + ε₁ + r₂ * (K' * r₁ * ∥res _ - N.d i' i n₁∥ + ε₂) : by rw mul_assoc
    ... ≤ K * _ + ε₁ + r₂ * (K' * r₁ * (K * ∥(N.d i (i+1)) _∥ + ε₁) + ε₂) :
      add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left
      hn₁ $ mul_nonneg K'.coe_nonneg r₁.coe_nonneg) _) r₂.coe_nonneg) _
    ... = (K + r₁ * r₂ * K * K') * ∥N.d i (i+1) (f m)∥ + ε₁ * (1 + K' * r₁ * r₂) + r₂ * ε₂ : by ring
    ... = (K + r₁ * r₂ * K * K') * ∥N.d i (i+1) (f m)∥ + ε / 2 + r₂ * ε₂ : by simp [hmulε₁]
    ... ≤ _ * ∥N.d i (i+1) (f m)∥ + ε / 2 + ε / 2 : add_le_add_left hle _
    ... = _ * ∥(M.d i (i+1)) m∥ + ε : by rw [add_assoc, add_halves', d_apply, hom_apply, hfnorm]
end

#lint
#exit






/- even more cleanups -/
lemma fexample (M N P : system_of_complexes) (k' K K' r₁ r₂ c : ℝ≥0)
  (i : ℕ) (ε : ℝ) (i' i'' : ℕ)
  (f : M ⟶ N)
  (g : N ⟶ P)
  [hk' : fact (1 ≤ k')]
  (hN_adm : N.admissible)
  (hgnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (N c i)), ∥g x∥ ≤ ↑r₁ * ∥x∥)
  (hfnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (M c i)), ∥(f.apply) x∥ = ∥x∥)
  (n₁ : N (k' * c) i')
  (p₂ : P c i'')
  (n₂ : N c i'')
  (hn₂ : g n₂ = p₂)
  (nnew₁ : N c i')
  (m₁ : M c i')
  (hii' : i' + 1 = i)
  {c₁ : ℝ≥0}
  {ε₁ ε₂ : ℝ}
  [fc₁ : fact (k' * c ≤ c₁)]
  [fc : fact (c ≤ c₁)]
  (m : (M c₁ i))
  (hmulε₁ : ε₁ * (1 + K' * r₁ * r₂) = ε / 2)
  (hle : (r₂ : ℝ) * ε₂ ≤ ε / 2)
--  {n : N c₁ i}
--  (hn₁ : n = f m)
       :
--    let nn : (N c₁ i) := f m
--     in
      ∥res (f m) - (N.d i' i) n₁∥ ≤ K * ∥(N.d i (i + 1)) (f m)∥ + ε₁ →
        (let p₁ : (P (k' * c) i') := g n₁
         in
          p₁ = g n₁ →
            ∥res p₁ - (P.d i'' i') p₂∥ ≤ K' * ∥(P.d i' (i' + 1)) p₁∥ + ε₂ →
            (let n₁' : (N c i') := (N.d i'' i') n₂
             in
              n₁' = (N.d i'' i') n₂ →
                ∥nnew₁∥ ≤ r₂ * ∥g (res n₁ - n₁')∥ →
                f m₁ = res n₁ - n₁' - nnew₁ →
                ∥g ((N.d i' i) n₁)∥ = ∥g (res (f m) - (N.d i' i) n₁)∥ →
                ∥res m - (M.d i' i) m₁∥ ≤ (K + r₁ * r₂ * K * K') * ∥(M.d i (i + 1)) m∥ + ε)) :=
begin
  intros --nn
  hn₁ p₁ hdefp₁ hp₂ n₁' hdefn₁' hnormnnew₁ hm₁ hfm,
   have hε₁ : 0 < ε₁, sorry,
    calc ∥res m - (M.d i' i) m₁∥ = ∥f (res m - (M.d i' i) m₁)∥ : (hfnorm _ _ _).symm
    ... = ∥res _ - (N.d i' i (res n₁) - N.d i' i (n₁' + nnew₁))∥ :
      by rw [hom_apply, normed_group_hom.map_sub, ←hom_apply, ←hom_apply, ←res_apply,
      ←d_apply, hm₁, sub_sub, normed_group_hom.map_sub]
    ... = ∥(res _ - N.d i' i (res n₁)) + N.d i' i (n₁' + nnew₁)∥ : by abel
    ... ≤ ∥res _ - N.d i' i _∥ + ∥N.d i' i (n₁' + nnew₁)∥ : norm_add_le _ _
    ... = ∥res _ - N.d i' i _∥ + ∥N.d i' i nnew₁∥ : by simp only [map_add, zero_add, d_d]
    ... ≤ ∥res _ - N.d i' i _∥ + r₂ * ∥g (res n₁ - n₁')∥ :
        add_le_add_left (le_trans (hN_adm.d_norm_noninc _ _ i' i nnew₁) hnormnnew₁) _
    ... = ∥res _ - N.d i' i _∥ + r₂ * ∥res p₁ - P.d i'' i' p₂∥ :
      by rw [hom_apply g, normed_group_hom.map_sub, ←hom_apply, ←hom_apply,
       ←res_apply _ _ g, hdefn₁', ←d_apply, hn₂]
    ... ≤ ∥res _ - N.d i' i _∥ + r₂ * (K' * ∥P.d i' (i'+1) p₁∥ + ε₂) :
      add_le_add_left (mul_le_mul_of_nonneg_left hp₂ r₂.coe_nonneg) _
    ... = _ + r₂ * (K' * ∥P.d i' (i'+1) p₁∥ + ε₂) :
      by rw [←res_res, d_res, normed_group_hom.map_sub]
    ... ≤ K * _ + ε₁ + r₂ * (K' * ∥P.d i' (i'+1) p₁∥ + ε₂) :
      add_le_add_right (le_trans (hN_adm.res_norm_noninc _ _ _ _ _) hn₁) _
    ... = K * _ + ε₁ + r₂ * (K' * ∥g (res (f m) - N.d i' i n₁)∥ + ε₂) :
      by rw [hdefp₁, d_apply _ _ g _, hii', hfm]
    ... ≤ K * _ + ε₁ + r₂ * (K' * (r₁ * ∥res (f m) - N.d i' i n₁∥) + ε₂) :
      add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left
      (hgnorm _ _ _) K'.coe_nonneg) _) $ r₂.coe_nonneg) _
    ... = K * _ + ε₁ + r₂ * (K' * r₁ * ∥res _ - N.d i' i n₁∥ + ε₂) : by rw mul_assoc
    ... ≤ K * _ + ε₁ + r₂ * (K' * r₁ * (K * ∥(N.d i (i+1)) _∥ + ε₁) + ε₂) :
      add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left
      hn₁ $ mul_nonneg K'.coe_nonneg r₁.coe_nonneg) _) r₂.coe_nonneg) _
    ... = (K + r₁ * r₂ * K * K') * ∥N.d i (i+1) (f m)∥ + ε₁ * (1 + K' * r₁ * r₂) + r₂ * ε₂ : by ring
    ... = (K + r₁ * r₂ * K * K') * ∥N.d i (i+1) (f m)∥ + ε / 2 + r₂ * ε₂ : by simp [hmulε₁]
    ... ≤ _ * ∥N.d i (i+1) (f m)∥ + ε / 2 + ε / 2 : add_le_add_left hle _
    ... = _ * ∥(M.d i (i+1)) m∥ + ε : by rw [add_assoc, add_halves', d_apply, hom_apply, hfnorm]
end

#lint
#exit



/- more cleanups -/
lemma fexample (M N P : system_of_complexes) ( --k
 k' K K' r₁ r₂ c : ℝ≥0)
  (i : ℕ) (ε : ℝ) (i' i'' : ℕ)
  (f : M ⟶ N)
  (g : N ⟶ P)
--  [hk : fact (1 ≤ k)]
  [hk' : fact (1 ≤ k')]
  (hN_adm : N.admissible)
  (hgnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (N c i)), ∥g x∥ ≤ ↑r₁ * ∥x∥)
  (hfnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (M c i)), ∥(f.apply) x∥ = ∥x∥)
  (n₁ : N (k' * c) i')
  (p₂ : P c i'')
  (n₂ : N c i'')
  (hn₂ : g n₂ = p₂)
  (nnew₁ : N c i')
  (m₁ : M c i')
  (hii' : i' + 1 = i)
  {c₁ : ℝ≥0}
  {ε₁ ε₂ : ℝ}
--  (hc₁ : c₁ = k * (k' * c))
--  (hε₁ : ε₁ = ε / 2 * (1 + K' * r₁ * r₂)⁻¹)
--  (hε₂ : ε₂ = ite (r₂ = 0) 1 (ε / 2 * (r₂)⁻¹))
  [fc₁ : fact (k' * c ≤ c₁)]
  [fc : fact (c ≤ c₁)]
   :
--     let --c₁ : ℝ≥0 := k * (k' * c),
--         ε₁ : ℝ := ε / 2 * (1 + K' * r₁ * r₂)⁻¹,
--         ε₂ : ℝ := ite (r₂ = 0) 1 (ε / 2 * (r₂)⁻¹)
--      in
       ∀ (m : (M c₁ i)),
            ε₁ * (1 + K' * r₁ * r₂) = ε / 2 →
                (r₂ : ℝ) * ε₂ ≤ ε / 2 →
                  (let n : (N c₁ i) := f m
                   in
                    ∥res n - (N.d i' i) n₁∥ ≤
                        K * ∥(N.d i (i + 1)) n∥ + ε₁ →
                      (let p₁ : (P (k' * c) i') := g n₁
                       in
                        p₁ = g n₁ →
                          ∥res p₁ - (P.d i'' i') p₂∥ ≤
                            K' * ∥(P.d i' (i' + 1)) p₁∥ + ε₂ →
                          (let n₁' : (N c i') := (N.d i'' i') n₂
                           in
                            n₁' = (N.d i'' i') n₂ →
                              ∥nnew₁∥ ≤
                                r₂ * ∥g (res n₁ - n₁')∥ →
                              f m₁ = res n₁ - n₁' - nnew₁ →
                              ∥g ((N.d i' i) n₁)∥ =
                                ∥g
                                    (res (f m) -
                                       (N.d i' i) n₁)∥ →
                              ∥res m - (M.d i' i) m₁∥ ≤
                                (K + r₁ * r₂ * K * K') * ∥(M.d i (i + 1)) m∥ +
                                  ε))) :=
begin
  intros --ε₁ ε₂
   m hmulε₁ hle n hn₁ p₁ hdefp₁ hp₂ n₁' hdefn₁' hnormnnew₁ hm₁ hfm,
   have hε₁ : 0 < ε₁, sorry,
    calc ∥res m - (M.d i' i) m₁∥ = ∥f (res m - (M.d i' i) m₁)∥ : (hfnorm _ _ _).symm
    ... = ∥res n - (N.d i' i (res n₁) - N.d i' i (n₁' + nnew₁))∥ :
      by rw [hom_apply, normed_group_hom.map_sub, ←hom_apply, ←hom_apply, ←res_apply,
      ←d_apply, hm₁, sub_sub, normed_group_hom.map_sub]
    ... = ∥(res n - N.d i' i (res n₁)) + N.d i' i (n₁' + nnew₁)∥ : by abel
    ... ≤ ∥res n - N.d i' i _∥ + ∥N.d i' i (n₁' + nnew₁)∥ : norm_add_le _ _
    ... = ∥res n - N.d i' i _∥ + ∥N.d i' i nnew₁∥ :
      by simp only [map_add, zero_add, d_d]
    ... ≤ ∥res n - N.d i' i _∥ + r₂ * ∥g (res n₁ - n₁')∥ :
        add_le_add_left (le_trans (hN_adm.d_norm_noninc _ _ i' i nnew₁) hnormnnew₁) _
    ... = ∥res n - N.d i' i _∥ + r₂ * ∥res p₁ - P.d i'' i' p₂∥ :
      by rw [hom_apply, normed_group_hom.map_sub, ←hom_apply, ←hom_apply, ←res_apply, hdefn₁', ←d_apply, hn₂]
    ... ≤ ∥res n - N.d i' i _∥ + r₂ * (K' * ∥P.d i' (i'+1) p₁∥ + ε₂) :
      add_le_add_left (mul_le_mul_of_nonneg_left hp₂ r₂.coe_nonneg) _
    ... = ∥_∥ + r₂ * (K' * ∥P.d i' (i'+1) p₁∥ + ε₂) :
      by rw [←res_res, d_res, normed_group_hom.map_sub]
    ... ≤ K * ∥N.d i (i+1) n∥ + ε₁ + r₂ * (K' * ∥P.d i' (i'+1) p₁∥ + ε₂) :
      add_le_add_right (le_trans (hN_adm.res_norm_noninc _ _ _ _ _) hn₁) _
    ... = K * ∥N.d i (i+1) n∥ + ε₁ + r₂ * (K' * ∥g (res (f m) - N.d i' i n₁)∥ + ε₂) :
      by rw [hdefp₁, d_apply _ _ g _, hii', hfm]
    ... ≤ K * ∥N.d i (i+1) n∥ + ε₁ + r₂ * (K' * (r₁ * ∥res (f m) - N.d i' i n₁∥) + ε₂) :
      add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left
      (hgnorm _ _ _) K'.coe_nonneg) _) $ r₂.coe_nonneg) _
    ... = K * ∥N.d i (i+1) n∥ + ε₁ + r₂ * (K' * r₁ * ∥res n - N.d i' i n₁∥ + ε₂) : by rw mul_assoc
    ... ≤ K * ∥N.d i (i+1) n∥ + ε₁ + r₂ * (K' * r₁ * (K * ∥(N.d i (i+1)) n∥ + ε₁) + ε₂) :
      add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left
      hn₁ $ mul_nonneg K'.coe_nonneg r₁.coe_nonneg) _) r₂.coe_nonneg) _
    ... = (K + r₁ * r₂ * K * K') * ∥N.d i (i+1) n∥ + ε₁ * (1 + K' * r₁ * r₂) + r₂ * ε₂ : by ring
    ... = (K + r₁ * r₂ * K * K') * ∥N.d i (i+1) (f m)∥ + ε / 2 + r₂ * ε₂ : by simp [hmulε₁]
    ... ≤ _ * ∥N.d i (i+1) (f m)∥ + ε / 2 + ε / 2 : add_le_add_left hle _
    ... = _ * ∥(M.d i (i+1)) m∥ + ε : by rw [add_assoc, add_halves', d_apply, hom_apply, hfnorm]
end

#lint
#exit



lemma fexample (M N P : system_of_complexes) (k k' K K' r₁ r₂ c : ℝ≥0)
  (i : ℕ) (ε : ℝ) (i' i'' : ℕ)
  (f : M ⟶ N)
  (g : N ⟶ P)
  [hk : fact (1 ≤ k)]
  [hk' : fact (1 ≤ k')]
  (hN_adm : N.admissible)
  (hgnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (N c i)), ∥g x∥ ≤ ↑r₁ * ∥x∥)
  (hfnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (M c i)), ∥(f.apply) x∥ = ∥x∥)
  (n₁ : N (k' * c) i')
  (p₂ : P c i'')
  (n₂ : N c i'')
  (hn₂ : g n₂ = p₂)
  (nnew₁ : N c i')
  (m₁ : M c i')
  (hii' : i' + 1 = i) :
     let c₁ : ℝ≥0 := k * (k' * c),
         ε₁ : ℝ := ε / 2 * (1 + K' * r₁ * r₂)⁻¹,
         ε₂ : ℝ := ite (r₂ = 0) 1 (ε / 2 * (r₂)⁻¹)
      in
       ∀ (m : (M c₁ i)),
            ε₁ * (1 + K' * r₁ * r₂) = ε / 2 →
--              0 < ε₁ →
                (r₂ : ℝ) * ε₂ ≤ ε / 2 →
                  (let n : (N c₁ i) := f m
                   in
                    ∥res n - (N.d i' i) n₁∥ ≤
                        K * ∥(N.d i (i + 1)) n∥ + ε₁ →
                      (let p₁ : (P (k' * c) i') := g n₁
                       in
                        p₁ = g n₁ →
                          ∥res p₁ - (P.d i'' i') p₂∥ ≤
                            K' * ∥(P.d i' (i' + 1)) p₁∥ + ε₂ →
                          (let n₁' : (N c i') := (N.d i'' i') n₂
                           in
                            n₁' = (N.d i'' i') n₂ →
                              ∥nnew₁∥ ≤
                                r₂ * ∥g (res n₁ - n₁')∥ →
                              f m₁ = res n₁ - n₁' - nnew₁ →
                              ∥g ((N.d i' i) n₁)∥ =
                                ∥g
                                    (res (f m) -
                                       (N.d i' i) n₁)∥ →
                              ∥res m - (M.d i' i) m₁∥ ≤
                                (K + r₁ * r₂ * K * K') * ∥(M.d i (i + 1)) m∥ +
                                  ε))) :=
begin
  intros c₁ ε₁ ε₂ m hmulε₁ --hε₁ ε₂
   hle n hn₁ p₁ hdefp₁ hp₂ n₁' hdefn₁' hnormnnew₁ hm₁ hfm,
   have hε₁ : 0 < ε₁, sorry,
    calc ∥res m - (M.d i' i) m₁∥ = ∥f (res m - (M.d i' i) m₁)∥ : (hfnorm _ _ _).symm
    ... = ∥res n - (N.d i' i (res n₁) - N.d i' i (n₁' + nnew₁))∥ :
      by rw [hom_apply, normed_group_hom.map_sub, ←hom_apply, ←hom_apply, ←res_apply,
      ←d_apply, hm₁, sub_sub, normed_group_hom.map_sub]
    ... = ∥(res n - N.d i' i (res n₁)) + N.d i' i (n₁' + nnew₁)∥ : by abel
    ... ≤ ∥res n - N.d i' i _∥ + ∥N.d i' i (n₁' + nnew₁)∥ : norm_add_le _ _
    ... = ∥res n - N.d i' i _∥ + ∥N.d i' i nnew₁∥ :
      by simp only [map_add, zero_add, d_d]
    ... ≤ ∥res n - N.d i' i _∥ + r₂ * ∥g (res n₁ - n₁')∥ :
        add_le_add_left (le_trans (hN_adm.d_norm_noninc _ _ i' i nnew₁) hnormnnew₁) _
    ... = ∥res n - N.d i' i _∥ + r₂ * ∥res p₁ - P.d i'' i' p₂∥ :
      by rw [hom_apply, normed_group_hom.map_sub, ←hom_apply, ←hom_apply, ←res_apply, hdefn₁', ←d_apply, hn₂]
    ... ≤ ∥res n - N.d i' i _∥ + r₂ * (K' * ∥P.d i' (i'+1) p₁∥ + ε₂) :
      add_le_add_left (mul_le_mul_of_nonneg_left hp₂ r₂.coe_nonneg) _
    ... = ∥_∥ + r₂ * (K' * ∥P.d i' (i'+1) p₁∥ + ε₂) :
      by rw [←res_res, d_res, normed_group_hom.map_sub]
    ... ≤ K * ∥N.d i (i+1) n∥ + ε₁ + r₂ * (K' * ∥P.d i' (i'+1) p₁∥ + ε₂) :
      add_le_add_right (le_trans (hN_adm.res_norm_noninc _ _ _ _ _) hn₁) _
    ... = K * ∥N.d i (i+1) n∥ + ε₁ + r₂ * (K' * ∥g (res (f m) - N.d i' i n₁)∥ + ε₂) :
      by rw [hdefp₁, d_apply _ _ g _, hii', hfm]
    ... ≤ K * ∥N.d i (i+1) n∥ + ε₁ + r₂ * (K' * (r₁ * ∥res (f m) - N.d i' i n₁∥) + ε₂) :
      add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left
      (hgnorm _ _ _) K'.coe_nonneg) _) $ r₂.coe_nonneg) _
    ... = K * ∥N.d i (i+1) n∥ + ε₁ + r₂ * (K' * r₁ * ∥res n - N.d i' i n₁∥ + ε₂) : by rw mul_assoc
    ... ≤ K * ∥N.d i (i+1) n∥ + ε₁ + r₂ * (K' * r₁ * (K * ∥(N.d i (i+1)) n∥ + ε₁) + ε₂) :
      add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left
      hn₁ $ mul_nonneg K'.coe_nonneg r₁.coe_nonneg) _) r₂.coe_nonneg) _
    ... = (K + r₁ * r₂ * K * K') * ∥N.d i (i+1) n∥ + ε₁ * (1 + K' * r₁ * r₂) + r₂ * ε₂ : by ring
    ... = (K + r₁ * r₂ * K * K') * ∥N.d i (i+1) (f m)∥ + ε / 2 + r₂ * ε₂ : by simp [hmulε₁]
    ... ≤ _ * ∥N.d i (i+1) (f m)∥ + ε / 2 + ε / 2 : add_le_add_left hle _
    ... = _ * ∥(M.d i (i+1)) m∥ + ε : by rw [add_assoc, add_halves', d_apply, hom_apply, hfnorm]
end

#lint
#exit
lemma fexample (M N P : system_of_complexes) (k k' K K' r₁ r₂ : ℝ≥0) --{a : ℕ}
  --{c₀ : ℝ≥0}
  (c : ℝ≥0) (i : ℕ) (ε : ℝ) (i' i'' : ℕ)
  (f : M ⟶ N)
  (g : N ⟶ P)
  [hk : fact (1 ≤ k)]
  [hk' : fact (1 ≤ k')]
--  (hN : N.is_weak_bounded_exact k K (a + 1) c₀) (hP : P.is_weak_bounded_exact k' K' (a + 1) c₀)
  (hN_adm : N.admissible)
  (hgnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (N c i)),
              ∥g x∥ ≤ ↑r₁ * ∥x∥)
/-
  (Hg : ∀ (c : ℝ≥0) [_inst_1 : fact (c₀ ≤ c)] (i : ℕ),
          i ≤ a + 1 + 1 →
          ∀ (y : (P c i)),
            ∃ (x : (N c i)),
              g x = y ∧ ∥x∥ ≤ ↑r₂ * ∥y∥)
  (hg : ∀ (c : ℝ≥0) (i : ℕ), range f.apply = ker g.apply)
  (hf : ∀ (c : ℝ≥0) (i : ℕ), isometry (f.apply))
-/
  (hfnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (M c i)),
              ∥(f.apply) x∥ = ∥x∥)
/-
  (hM_adm : M.admissible)
  (hc : fact (c₀ ≤ c))
  (hi : i ≤ a)
  (hε : ε > 0)
  (hlt : 0 < 1 + K' * r₁ * r₂)
  (hi' : i' = i - 1)
-/
  (n₁ : (N (k' * c) i'))
/-
  (Hi' : i' ≤ a + 1)
  (hi'' : i'' = i' - 1)
-/
  (p₂ : (P c i''))
--  (Hi'' : i'' ≤ a + 1 + 1)
  (n₂ : (N c i''))
  (hn₂ : g n₂ = p₂)
--  (hnormn₂ : ∥n₂∥ ≤ r₂ * ∥p₂∥)
  (nnew₁ : (N c i'))
  (m₁ : (M c i'))
--  (hizero : ¬i = 0)
  (hii' : i' + 1 = i) :
  let Knew : ℝ≥0 := K + r₁ * r₂ * K * K'
  in
    0 ≤ Knew →
     (let c₁ : ℝ≥0 := k * (k' * c),
          c₂ : ℝ≥0 := k' * c
      in
       ∀ (m : (M c₁ i)),
           let ε₁ : ℝ := ε / 2 * (1 + K' * r₁ * r₂)⁻¹
           in
            ε₁ * (1 + K' * r₁ * r₂) = ε / 2 →
              0 < ε₁ →
              (let ε₂ : ℝ := ite (r₂ = 0) 1 (ε / 2 * (r₂)⁻¹)
               in
                (r₂ : ℝ) * ε₂ ≤ ε / 2 →
                  0 < ε₂ →
                  (let n : (N c₁ i) := f m
                   in
                    ∥res n - (N.d i' i) n₁∥ ≤
                        K * ∥(N.d i (i + 1)) n∥ + ε₁ →
                      (let p₁ : (P (k' * c) i') := g n₁
                       in
                        p₁ = g n₁ →
                          ∥res p₁ - (P.d i'' i') p₂∥ ≤
                            K' * ∥(P.d i' (i' + 1)) p₁∥ + ε₂ →
                          (let n₁' : (N c i') := (N.d i'' i') n₂
                           in
                            n₁' = (N.d i'' i') n₂ →
                              g nnew₁ = g (res n₁ - n₁') →
                              ∥nnew₁∥ ≤
                                r₂ * ∥g (res n₁ - n₁')∥ →
--                              res n₁ - n₁' - nnew₁ ∈
--                                range f.apply →
                              f m₁ = res n₁ - n₁' - nnew₁ →
                              ∥g ((N.d i' i) n₁)∥ =
                                ∥g
                                    (res (f m) -
                                       (N.d i' i) n₁)∥ →
                              ∥res m - (M.d i' i) m₁∥ ≤
                                Knew * ∥(M.d i (i + 1)) m∥ +
                                  ε))))) :=
/-
   true))))) :=
-/
begin
  intros Knew bound_nonneg c₁ c₂ m ε₁ hmulε₁ hε₁ ε₂ hle hε₂ n hn₁ p₁ hdefp₁ hp₂ n₁' hdefn₁' hnnew₁ hnormnnew₁
  -- hker
   hm₁ hfm,
    calc ∥res m - (M.d i' i) m₁∥ = ∥f (res m - (M.d i' i) m₁)∥ : (hfnorm _ _ _).symm
    ... = ∥res n - (N.d i' i (res n₁) - N.d i' i (n₁' + nnew₁))∥ :
      by rw [hom_apply, normed_group_hom.map_sub, ←hom_apply, ←hom_apply, ←res_apply,
      ←d_apply, hm₁, sub_sub, normed_group_hom.map_sub]
    ... = ∥(res n - N.d i' i (res n₁)) + N.d i' i (n₁' + nnew₁)∥ : by abel
    ... ≤ ∥res n - N.d i' i (@res _ c₂ c _ _ n₁)∥ + ∥N.d i' i (n₁' + nnew₁)∥ : norm_add_le _ _
    ... = ∥res n - N.d i' i (@res _ c₂ c _ _ n₁)∥ + ∥N.d i' i nnew₁∥ :
      by simp only [map_add, zero_add, d_d]
    ... ≤ ∥res n - N.d i' i (@res _ c₂ c _ _ n₁)∥ + r₂ * ∥g (res n₁ - n₁')∥ :
        add_le_add_left (le_trans (hN_adm.d_norm_noninc _ _ i' i nnew₁) hnormnnew₁) _
    ... = ∥res n - N.d i' i (@res _ c₂ c _ _ n₁)∥ + r₂ * ∥res p₁ - P.d i'' i' p₂∥ :
      by rw [hom_apply, normed_group_hom.map_sub, ←hom_apply, ←hom_apply, ←res_apply, hdefn₁', ←d_apply, hn₂]
    ... ≤ ∥res n - N.d i' i (@res _ c₂ c _ _ n₁)∥ + r₂ * (K' * ∥P.d i' (i'+1) p₁∥ + ε₂) :
      add_le_add_left (mul_le_mul_of_nonneg_left hp₂ $ nnreal.coe_nonneg r₂) _
    ... = ∥@res _ c₂ c _ _ (@res _ c₁ c₂ _ _ n - N.d i' i n₁)∥ + r₂ * (K' * ∥P.d i' (i'+1) p₁∥ + ε₂) :
      by rw [←@res_res _ c₁ c₂ c _ _ _ n, d_res, normed_group_hom.map_sub]
    ... ≤ K * ∥N.d i (i+1) n∥ + ε₁ + r₂ * (K' * ∥P.d i' (i'+1) p₁∥ + ε₂) :
      add_le_add_right (le_trans (hN_adm.res_norm_noninc _ _ _ _ _) hn₁) _
    ... = K * ∥N.d i (i+1) n∥ + ε₁ + r₂ * (K' * ∥g (res (f m) - N.d i' i n₁)∥ + ε₂) :
      by rw [hdefp₁, d_apply _ _ g _, hii', hfm]
    ... ≤ K * ∥N.d i (i+1) n∥ + ε₁ + r₂ * (K' * (r₁ * ∥res (f m) - N.d i' i n₁∥) + ε₂) :
      add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left
      (hgnorm _ _ _) $ nnreal.coe_nonneg K') _) $ nnreal.coe_nonneg r₂) _
    ... = K * ∥N.d i (i+1) n∥ + ε₁ + r₂ * (K' * r₁ * ∥res n - N.d i' i n₁∥ + ε₂) : by rw mul_assoc
    ... ≤ K * ∥N.d i (i+1) n∥ + ε₁ + r₂ * (K' * r₁ * (K * ∥(N.d i (i+1)) n∥ + ε₁) + ε₂) :
      add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left
      hn₁ $ mul_nonneg (nnreal.coe_nonneg K') (nnreal.coe_nonneg r₁)) _) $ nnreal.coe_nonneg r₂) _
    ... = (K + r₁ * r₂ * K * K') * ∥N.d i (i+1) n∥ + ε₁ * (1 + K' * r₁ * r₂) + r₂ * ε₂ : by ring
    ... = Knew * ∥N.d i (i+1) (f m)∥ + ε / 2 + r₂ * ε₂ : by simp [hmulε₁]
    ... ≤ Knew * ∥N.d i (i+1) (f m)∥ + ε / 2 + ε / 2 : add_le_add_left hle _
    ... = Knew * ∥(M.d i (i+1)) m∥ + ε : by rw [add_assoc, add_halves', d_apply, hom_apply, hfnorm]
end
#lint




#exit



/- Works! -/
lemma ggexample (M N : system_of_complexes) (k k' K K' r₁ r₂ : ℝ≥0) {a : ℕ}
   (c : ℝ≥0) (ε : ℝ) (i' i'' : ℕ)
  (f : M ⟶ N)
  [hk : fact (1 ≤ k)]
  [hk' : fact (1 ≤ k')]
  (hfnorm : ∀ (c : ℝ≥0) (i : ℕ) (x : (M c i)), ∥(f.apply) x∥ = ∥x∥)
  (hM_adm : M.admissible)
  (hε : ε > 0)
  (hlt : (0 : ℝ) < 1 + K' * r₁ * r₂)
  (n₁ : (N (k' * c) i'))
  (Hi' : i' ≤ a + 1)
  (hi'' : i'' = i' - 1)
  (nnew₁ : (N c i'))
  (m₁ : (M c i'))
  (hi' : i' = 0 - 1)
  {ε₁ : ℝ}
  (hmulε₁ : ε₁ * (1 + K' * r₁ * r₂) = ε / 2) :
--  let
--    ε₁ : ℝ := ε / 2 * (1 + K' * r₁ * r₂)⁻¹
--      in ε₁ * (1 + K' * r₁ * r₂) = ε / 2 →
--      0 < ε₁ →
      ( ∀ (m : (M (k * (k' * c)) 0)),
          --let n : (N (k * (k' * c)) 0) := f m
          --in
           ∥res (f m) - (N.d i' 0) n₁∥ ≤ K * ∥(N.d 0 (0 + 1)) (f m)∥ + ε₁ →
             ∥res m - (M.d i' 0) m₁∥ ≤ (K + r₁ * r₂ * K * K') * ∥(M.d 0 (0 + 1)) m∥ + ε) :=
begin
intros --ε₁ hmulε₁
-- hε₁
  m hn₁,
    rw [nat.zero_sub] at hi',
    subst hi',
    simp only [d_self_apply, sub_zero, nnreal.coe_add, nnreal.coe_mul] at hn₁ ⊢,
    rw [res_apply, hom_apply f (res m), hfnorm] at hn₁,
    rw ←@res_res _ _ (k' * c) c _ _ _ _,
    refine le_trans (hM_adm.res_norm_noninc _ _ _ _ _) (le_trans hn₁ _),
    have : (↑K + ↑r₁ * ↑r₂ * ↑K * ↑K') * ∥M.d 0 1 m∥ + ε =
      ↑K * ∥M.d 0 1 m∥ + (↑r₁ * ↑r₂ * ↑K * ↑K' * ∥M.d 0 1 m∥ + ε) := by ring,
    rw [d_apply, hom_apply f _, hfnorm, this],
    have hmul : (↑r₁ * ↑r₂ * ↑K * ↑K' * ∥M.d 0 1 m∥ + (ε / 2 + ε / 2)) * (1 + ↑K' * ↑r₁ * ↑r₂) =
      (ε / 2) + ((ε / 2) + (↑r₁ * ↑r₂ * ↑K * ↑K' * ∥M.d 0 1 m∥ +
      ↑r₁ * ↑r₂ * ↑K * ↑K' * ∥M.d 0 1 m∥ * ↑K' * ↑r₁ * ↑r₂ +
      ε * (↑K' * ↑r₁ * ↑r₂))) := by ring,
    refine add_le_add_left ((mul_le_mul_right hlt).1 _) _,
    rw [←add_halves' ε, hmulε₁, hmul, ←coe_nnnorm],
--    apply (le_add_iff_nonneg_right _).mpr,
--    norm_cast,
--    norm_num,
--    apply (le_add_iff_nonneg_right _).2,
    exact_mod_cast (le_add_iff_nonneg_right (ε / 2)).2 (add_nonneg (half_pos hε).le
      (add_nonneg (nnreal.coe_nonneg _) (mul_nonneg (gt.lt hε).le (nnreal.coe_nonneg _)))),
end
#lint

#exit
