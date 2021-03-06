import tactic.induction
import data.nat.prime
import data.nat.modeq
import logic.function.iterate

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

lemma digital_root_eq {n : ℕ} :
  digital_root n = ite (n % 9 = 0) 9 (n % 9) :=
begin
  sorry
end

lemma num_3_dvd_of_mod_9_eq_3_or_6 {n : ℕ}
  (h : n % 9 = 3 ∨ n % 9 = 6) : 3 ∣ n :=
begin
  have h₁ : n % 9 % 3 = 0, { cases h; rw h; dec_trivial },
  rw nat.mod_mod_of_dvd at h₁, swap, { dec_trivial },
  exact nat.dvd_of_mod_eq_zero h₁,
end

lemma num_3_dvd_of_mod_9_eq_3 {n : ℕ} (h : n % 9 = 3) : 3 ∣ n :=
num_3_dvd_of_mod_9_eq_3_or_6 (or.inl h)

lemma num_3_dvd_of_mod_9_eq_6 {n : ℕ} (h : n % 9 = 6) : 3 ∣ n :=
num_3_dvd_of_mod_9_eq_3_or_6 (or.inr h)

lemma prime_mod_9 {n : ℕ}
  (h₁ : 3 < n)
  (h₂ : prime n) :
  n % 9 ∈ ({1, 2, 4, 5, 7, 8} : set ℕ) :=
begin
  rw ←nat.prime_iff at h₂, replace h₂ := h₂.2,
  obtain ⟨n, rfl⟩ := nat.exists_eq_add_of_lt h₁,
  let k := n + 4, replace h₁ : 3 + n + 1 = k, { rw [add_comm 3, add_assoc] },
  generalize hm : k % 9 = m, rw h₁ at h₂ ⊢, rw hm, replace h₁ : m < 9,
  { rw ←hm, exact nat.mod_lt _ dec_trivial }, cases m,
  { specialize h₂ 3 (k / 3), have h₃ : 3 * 3 ∣ k := nat.dvd_of_mod_eq_zero hm,
    have h₄ : k / 3 * 3 = k := nat.div_mul_cancel (dvd_of_mul_left_dvd h₃),
    rw mul_comm at h₄, specialize h₂ h₄.symm, simp at h₂, rw h₂ at h₄,
    rw ←h₄ at h₃, contrapose h₃, dec_trivial },
  cases m, { simp }, cases m, { simp }, cases m,
  { specialize h₂ 3 (k / 3), have h₃ : 3 ∣ k := num_3_dvd_of_mod_9_eq_3 hm,
    have h₄ : k / 3 * 3 = k := nat.div_mul_cancel h₃, rw mul_comm at h₄,
    specialize h₂ h₄.symm, simp at h₂, rw h₂ at h₄, cases h₄ },
  cases m, { simp }, cases m, { simp }, cases m,
  { specialize h₂ 3 (k / 3), have h₃ : 3 ∣ k := num_3_dvd_of_mod_9_eq_6 hm,
    have h₄ : k / 3 * 3 = k := nat.div_mul_cancel h₃, rw mul_comm at h₄,
    specialize h₂ h₄.symm, simp at h₂,rw h₂ at h₄, cases h₄ },
  cases m, { simp }, cases m, { simp },
  change m + 9 < 9 at h₁, contrapose! h₁, exact le_add_self,
end

example {n : ℕ}
  (h₁ : 3 < n)
  (h₂ : prime n)
  (h₃ : prime (n + 2)) :
  digital_root (n * (n + 2)) = 8 :=
begin
  rw digital_root_eq,
  split_ifs with hx,
  {
    exfalso,
    rw [nat.mul_mod, ←nat.dvd_iff_mod_eq_zero] at hx,
    cases hx with x hx,
    sorry
  },
  sorry;{ rw [nat.mul_mod, nat.add_mod],
    have hn : 3 < n + 2 := lt_trans h₁ (lt_add_of_pos_right n dec_trivial),
    replace h₂ := prime_mod_9 h₁ h₂, replace h₃ := prime_mod_9 hn h₃,
    rw nat.add_mod at h₃, rcases h₂ with h | h | h | h | h | h; change _ = _ at h;
    { rw h at h₃, contrapose h₃, simp, try { dec_trivial }} <|>
    { rw h, dec_trivial }},
end