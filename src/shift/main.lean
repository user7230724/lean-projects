import tactic
import tactic.induction
import data.nat.pow
import data.nat.parity
import data.nat.lattice
import data.nat.modeq

noncomputable theory
open_locale classical

def shift (n : ℕ) : ℕ :=
Inf {k : ℕ | odd k ∧ ∃ (p : ℕ), k * 2 ^ p = n}

lemma shift_0 : shift 0 = 0 :=
begin
  simp_rw [shift, nat.Inf_eq_zero],
  right, ext n, simp, rintro h k, push_neg, split,
  { rintro rfl, contrapose! h, exact even_zero },
  { intro h₁, clear' n h, induction k with k ih,
    { cases h₁ },
    { apply ih, clear ih, change 2 * 2 ^ k = 2 * 0 at h₁,
      rwa nat.mul_right_inj (dec_trivial : 0 < 2) at h₁ }},
end

lemma shift_1 : shift 1 = 1 :=
begin
  have h : {k : ℕ | odd k ∧ ∃ (p : ℕ), k * 2 ^ p = 1}.nonempty,
  { use 1, simp, use 0, dec_trivial },
  rw [shift, nat.Inf_def h, nat.find_eq_iff], dsimp, clear h,
  refine ⟨⟨odd_one, _⟩, _⟩,
  { use 0, dec_trivial },
  { push_neg, rintro n h₁ h₂ p, cases n, { simp },
    contrapose h₁, simp },
end

lemma shift_mul_2 {n : ℕ} :
  shift (n * 2) = shift n :=
begin
  generalize h : shift n = r, rw shift at h ⊢,
  by_cases h₁ : {k : ℕ | odd k ∧ ∃ (p : ℕ), k * 2 ^ p = n}.nonempty,
  { have h₂ : {k : ℕ | odd k ∧ ∃ (p : ℕ), k * 2 ^ p = n * 2}.nonempty,
    { rcases h₁ with ⟨k, h₁, p, h₂⟩, use [k, h₁, p + 1],
      simp [pow_succ], linarith },
    rw nat.Inf_def h₁ at h, rw nat.Inf_def h₂,
    simp_rw nat.find_eq_iff at h ⊢, clear' h₁ h₂,
    rcases h with ⟨⟨h₁, p, h₂⟩, h₃⟩, simp at *, refine ⟨⟨h₁, _⟩, _⟩,
    { use p + 1, rw [pow_succ, ←mul_assoc, mul_comm r 2, mul_assoc, mul_comm n 2],
      congr, exact h₂ },
    { rintro a h₁ h₂ b, cases b,
      { rw [pow_zero, mul_one], rintro rfl, contrapose! h₂,
        rw even, use n, rw mul_comm },
      { rw [pow_succ, ←mul_assoc, mul_comm _ 2, mul_assoc, mul_comm _ 2],
        rw nat.mul_right_inj (dec_trivial : 0 < 2), apply h₃; assumption }}},
  { have h₂ : ¬{k : ℕ | odd k ∧ ∃ (p : ℕ), k * 2 ^ p = n * 2}.nonempty,
    { contrapose! h₁, cases h₁ with k h₁, use k, simp at h₁ ⊢, clear' r h,
      rcases h₁ with ⟨h₁, p, h₂⟩, use h₁, rw ←nat.odd_iff_not_even at h₁,
      rcases h₁ with ⟨k, rfl⟩, cases p,
      { exfalso, simp at h₂, replace h₂ := congr_arg (λ n, n % 2) h₂,
        contrapose! h₂, simp [nat.add_mod] },
      use p, simp [pow_succ] at h₂, linarith },
    rw set.not_nonempty_iff_eq_empty at h₂, cases r,
    { rw nat.Inf_eq_zero, simp, simp_rw ←nat.odd_iff_not_even, exact h₂ },
    have h₃ := nat.nonempty_of_Inf_eq_succ h, contradiction },
end

lemma not_even_mul_2_add_1 {n : ℕ} : ¬even (n * 2 + 1) :=
begin
  rw even, push_neg, rintro k h, replace h := congr_arg (λ n, n % 2) h,
  simp [nat.add_mod] at h, exact h,
end

lemma shift_mul_2_add_1 {n : ℕ} :
  shift (n * 2 + 1) = n * 2 + 1 :=
begin
  rw shift, have h : {k : ℕ | odd k ∧ ∃ (p : ℕ), k * 2 ^ p = n * 2 + 1}.nonempty,
  { use n * 2 + 1, simp, use [not_even_mul_2_add_1, 0], simp },
  rw [nat.Inf_def h, nat.find_eq_iff], clear h, simp,
  refine ⟨⟨not_even_mul_2_add_1, _⟩, _⟩,
  { use 0, simp },
  { rintro k h₁ h₂ p, rw ←nat.odd_iff_not_even at h₂,
    rcases h₂ with ⟨k, rfl⟩, cases p,
    { apply ne_of_lt, simp at *, exact h₁ },
    { rw pow_succ, intro h₂, replace h₂ := congr_arg (λ n, n % 2) h₂,
      simp [nat.add_mod, nat.mul_mod] at h₂, exact h₂ }},
end

lemma shift_def {n : ℕ} :
  shift n = if 1 < n ∧ n % 2 = 0 then shift (n / 2) else n :=
begin
  split_ifs,
  { cases h with h₁ h₂, rw [←nat.even_iff, even] at h₂,
    rcases h₂ with ⟨n, rfl⟩, clear h₁, simp, rw mul_comm, exact shift_mul_2 },
  { rw not_and_distrib at h, cases h,
    { cases n, { exact shift_0 },
      cases n, { exact shift_1 },
      contrapose h, push_neg, simp },
    { rw [←nat.even_iff, ←nat.odd_iff_not_even, odd] at h,
      rcases h with ⟨n, rfl⟩, rw mul_comm, exact shift_mul_2_add_1 }},
end