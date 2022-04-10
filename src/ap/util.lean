import tactic.induction
import data.nat.parity
import data.int.basic
import data.set.basic
import data.set.finite
import data.list

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