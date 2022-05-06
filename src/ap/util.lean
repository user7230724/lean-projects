import tactic.induction
import data.nat.parity
import data.int.interval
import data.set.finite
import data.list
import data.finset
import set_theory.cardinal.basic

noncomputable theory
open_locale classical

@[reducible]
def snoc {α : Type*} (xs : list α) (x : α) : list α :=
xs ++ [x]

lemma snoc_eq_snoc_iff {α : Type*} {xs ys : list α} {x y : α} :
  snoc xs x = snoc ys y ↔ xs = ys ∧ x = y :=
begin
  split; intro h,
  { simp_rw [list.append_eq_append_iff] at h, cases h; rcases h with ⟨zs, h₁, h₂⟩;
    { have h₃ := congr_arg list.length h₂, simp at h₃,
      rw list.length_eq_zero at h₃, cases h₃, simp at h₁ h₂,
      exact ⟨h₁.symm, h₂⟩ <|> exact ⟨h₁, h₂.symm⟩ }},
  { rw [h.1, h.2] },
end

lemma length_snoc {α : Type*} {xs : list α} {x : α} :
  (snoc xs x).length = xs.length.succ :=
by { rw [list.length_append], refl }

lemma length_lt_length_append_cons {α : Type*} {xs ys : list α} {y : α} :
  xs.length < (xs ++ y :: ys).length :=
begin
  rw [list.length_append, list.length_cons], change _ + 0 < _,
  rw add_lt_add_iff_left, exact (list.length ys).succ_pos,
end

lemma length_lt_length_append_snoc {α : Type*} {xs ys : list α} {y : α} :
  xs.length < (xs ++ snoc ys y).length :=
begin
  rw [list.length_append, length_snoc], change _ + 0 < _,
  rw add_lt_add_iff_left, exact (list.length ys).succ_pos,
end

lemma length_lt_length_snoc {α : Type*} {xs : list α} {x : α} :
  xs.length < (snoc xs x).length :=
length_lt_length_append_cons

lemma length_lt_length_snoc₂ {α : Type*} {xs : list α} {x y : α} :
  xs.length < (snoc (snoc xs x) y).length :=
by { transitivity (snoc xs x).length; exact length_lt_length_snoc }

lemma exi_ge_of_set_inf {P : ℕ → Prop} {n : ℕ}
  (h : {n : ℕ | P n}.infinite) : ∃ (k : ℕ), n ≤ k ∧ P k :=
begin
  obtain ⟨k, h₁, h₂⟩ := h.exists_nat_lt n,
  exact ⟨k, nat.le_of_lt h₂, h₁⟩,
end

lemma exi_set_infinite_of_forall_exi_P {α β : Type} {P : α → β → Prop}
  (h₁ : (set.univ : set α).infinite)
  (h₂ : (set.univ : set β).finite)
  (h₃ : ∀ (a : α), ∃ (b : β), P a b) :
  ∃ (b : β), {a : α | P a b}.infinite :=
begin
  by_contra' h₄, simp_rw set.not_infinite at h₄,
  have h₅ : {a : α | ∃ (b : β), P a b}.finite,
  { convert_to (⋃ (b : β), {a : α | P a b}).finite, { ext a, simp, },
    convert_to (⋃ (b : β) (h : b ∈ set.univ), {a : α | P a b}).finite,
    { congr, ext b a, simp, intros, apply set.mem_univ },
    apply set.finite.bUnion h₂, intros, apply h₄ },
  replace h₅ : (set.univ : set α).finite,
  { convert h₅, ext a, simp, exact h₃ a },
  contradiction,
end

lemma exi_set_infinite_of_forall_exi_P_nat {α : Type} [fintype α]
  {P : ℕ → α → Prop}
  (h : ∀ (n : ℕ), ∃ (a : α), P n a) :
  ∃ (a : α), {n : ℕ | P n a}.infinite :=
begin
  fapply exi_set_infinite_of_forall_exi_P,
  { exact set.infinite_univ },
  { exact set.finite_univ },
  { exact h },
end

lemma fintype_subtype_of_set_finite {α : Type} {P : α → Prop}
  (h : {x : α | P x}.finite) : fintype {x : α // P x} :=
begin
  apply set.fintype_of_univ_finite, rw set.univ_subtype,
  apply set.finite.bUnion h, simp,
end

lemma set_finite_of_set_equiv_finite' {α β : Type} (e : α ≃ β) {P : α → Prop}
  (h : {x : α | P x}.finite) : {y : β | P (e.inv_fun y)}.finite :=
begin
  fapply set.finite_of_finite_image,
  { exact α },
  { exact e.inv_fun },
  { apply set.inj_on_of_injective,
    exact function.right_inverse.injective e.right_inv },
  { convert h, ext a, split; intro h₁,
    { rcases h₁ with ⟨b, h₁, h₂⟩, subst h₂, exact h₁ },
    { use e.to_fun a, fsplit,
      { change P _, convert h₁, exact e.left_inv a },
      { exact e.left_inv a }}},
end

lemma set_finite_of_set_equiv_finite {α β : Type} (e : α ≃ β) {P : β → Prop}
  (h : {x : α | P (e.to_fun x)}.finite) : {y : β | P y}.finite :=
begin
  replace h := set_finite_of_set_equiv_finite' e h, dsimp at h, convert h,
  funext y, congr, exact eq.symm (e.right_inv y),
end

lemma abs_le_finite {d : ℤ} : {a : ℤ | |a| ≤ d}.finite :=
by { simp_rw abs_le, apply set.finite_Icc }

lemma abs_sub_le_finite {c d : ℤ} : {a : ℤ | |a - c| ≤ d}.finite :=
begin
  fapply set.finite.of_preimage,
  { exact ℤ },
  { intro a, exact a + c },
  { simp, exact abs_le_finite },
  { intro a, use a - c, simp },
end

lemma nat_find_le_find_of_imp {P Q : ℕ → Prop}
  {hh₁ : ∃ (n : ℕ), P n}
  {hh₂ : ∃ (n : ℕ), Q n}
  (h : ∀ (n : ℕ), Q n → P n) :
  nat.find hh₁ ≤ nat.find hh₂ :=
begin
  let n := _, change n ≤ _, by_cases h₁ : Q n,
  { apply le_of_eq, symmetry, rw nat.find_eq_iff, use h₁, rintro k h₂,
    have h₃ : nat.find hh₁ = n := rfl, rw nat.find_eq_iff at h₃,
    replace h₃ := h₃.2 k h₂, contrapose! h₃, exact h _ h₃ },
  { have h₂ : ∀ (k : ℕ), Q k → n ≤ k,
    { rintro k h₂, by_contra' hh, have h₃ : nat.find hh₁ = n := rfl,
      rw nat.find_eq_iff at h₃, apply h₃.2 k hh, exact h _ h₂ },
    apply h₂, apply nat.find_spec },
end

lemma nat_Inf_le_Inf_of_subset {P Q : set ℕ}
  (h₁ : Q.nonempty)
  (h₂ : Q ⊆ P) :
  Inf P ≤ Inf Q :=
begin
  have h₃ : ∃ n, n ∈ Q,
  { cases h₁ with n h₁, use [n, h₁] },
  have h₄ : ∃ n, n ∈ P,
  { cases h₃ with n h₃, use n, apply h₂, exact h₃ },
  simp_rw Inf, split_ifs, exact nat_find_le_find_of_imp h₂,
end

lemma finset_card_insert_erase_eq {α : Type} {s : finset α} {x y : α}
  (h₁ : x ∈ s)
  (h₂ : y ∉ s) :
  (insert y (s.erase x)).card = s.card :=
begin
  replace h₂ : y ∉ s.erase x,
  { rw finset.mem_erase, tauto },
  rw [finset.card_insert_of_not_mem h₂, finset.card_erase_of_mem h₁],
  cases h₃ : s.card,
  { rw finset.card_eq_zero at h₃, subst h₃, cases h₁ },
  { refl },
end