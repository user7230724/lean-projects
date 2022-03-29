import tactic.induction
import logic.function.iterate
import data.list.basic

noncomputable theory
open_locale classical

def get_some {α : Type} [inhabited α] (P : α → Prop) : α :=
if h : ∃ (x : α), P x then h.some else default

def reduce {α : Type} [inhabited α] (f : α → α) (x : α) : α := get_some
(λ (r : α), ∃ (n : ℕ), (f^[n]) x = r ∧ (f^[n + 1]) x = r)

def digits (n : ℕ) : list ℕ := get_some
(λ (ds : list ℕ), (∀ (d ∈ ds), d ≤ 9) ∧ ds.foldl (λ a d, a * 10 + d) 0 = n)

def digits_sum (n : ℕ) : ℕ := (digits n).sum
def digital_root (n : ℕ) : ℕ := reduce digits_sum n

lemma exi_digits {n : ℕ} : ∃ (ds : list ℕ),
  (∀ (d ∈ ds), d ≤ 9) ∧ ds.foldl (λ a d, a * 10 + d) 0 = n :=
begin
  use (nat.to_digits 10 n).reverse,
  fsplit,
  {
    rintro d h,
    rw list.mem_reverse at h,
    induction n with n ih generalizing d,
    {
      change d = 0 ∨ false at h,
      simp at h,
      cases h,
      dec_trivial,
    },
    {
      change d ∈ nat.digit_succ _ _ at h,
      generalize h₁ : nat.to_digits 10 n = xs,
      rw h₁ at h ih,
      induction' xs,
      {
        change d = 1 ∨ false at h,
        simp at h,
        rw h,
        dec_trivial,
      },
      {
        change d ∈ ite _ _ _ at h,
        split_ifs at h with h₂,
        {
          apply ih,
          sorry
        },
        sorry,
      },
    },
  },
  sorry
end

-- #exit

lemma digital_root_eq {n : ℕ} :
  digital_root n = ite (n % 9 = 0) 9 (n % 9) :=
begin
  sorry
end