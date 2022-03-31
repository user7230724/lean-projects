import tactic.induction
import data.int.basic
import data.set.basic
import data.list

noncomputable theory
open_locale classical

lemma snoc_eq_snoc_iff {α : Type*} {xs ys : list α} {x y : α} :
  xs ++ [x] = ys ++ [y] ↔ xs = ys ∧ x = y :=
begin
  split; intro h,
  { rw list.append_eq_append_iff at h, cases h; rcases h with ⟨zs, h₁, h₂⟩;
    { have h₃ := congr_arg list.length h₂, simp at h₃,
      rw list.length_eq_zero at h₃, cases h₃, simp at h₁ h₂,
      exact ⟨h₁.symm, h₂⟩ <|> exact ⟨h₁, h₂.symm⟩ }},
  { rw [h.1, h.2] },
end