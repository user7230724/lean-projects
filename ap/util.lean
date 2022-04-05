import tactic.induction
import data.int.basic
import data.set.basic
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