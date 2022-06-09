import tactic
import tactic.induction
import logic.function.iterate
import data.list.basic

noncomputable theory
open_locale classical

def get_some {α : Type} [inhabited α] (P : α → Prop) : α :=
if h : ∃ (x : α), P x then h.some else default

def repeated {α : Type} [inhabited α] (f : α → α) (z : α) : α :=
get_some (λ (x : α), ∃ (n : ℕ), (f^[n]) z = x ∧ (f^[n + 1]) z = x)

def get_digits (n : ℕ) : list ℕ :=
get_some (λ (l : list ℕ), l.foldl (λ (a b : ℕ), a * 10 + b) 0 = n)

def sum_digits (n : ℕ) : ℕ := (get_digits n).sum

def digital_root (n : ℕ) : ℕ := repeated sum_digits n

-----

lemma get_some_pos {α : Type} [inhabited α] {P : α → Prop}
  (h : ∃ (x : α), P x) : get_some P = h.some :=
dif_pos h

lemma get_some_eq_get_some_of_exists_iff {α β : Type} [inhabited α]
  {P₁ P₂ : α → Prop} {f : α → β}
  (h₁ : (∃ (x : α), P₁ x) ↔ (∃ (x : α), P₂ x))
  (h₂ : ∀ (h₁ : ∃ (x : α), P₁ x) (h₂ : ∃ (x : α), P₂ x), f h₁.some = f h₂.some) :
  f (get_some P₁) = f (get_some P₂) :=
begin
  simp_rw [get_some, h₁], split_ifs with h₃,
  { apply h₂ },
  { refl },
end

def reversed {α : Type} (f : list α → list α) (l : list α) : list α :=
(f l.reverse).reverse

def trim_start : list ℕ → list ℕ
| (0::l) := l
| l := l

def trim_end : list ℕ → list ℕ :=
reversed trim_start

lemma exi_eq_append_zeros_of_foldr_eq_foldr {l₁ l₂ : list ℕ}
  (h : l₁.foldr (λ (a b : ℕ), a + b * 10) 0 = l₂.foldr (λ (a b : ℕ), a + b * 10) 0) :
  ∃ (l : list ℕ) (n₁ n₂ : ℕ), l₁ = l ++ list.repeat 0 n₁ ∧ l₂ = l ++ list.repeat 0 n₂ :=
begin
  let l := trim_end l₁,
  refine ⟨l, l₁.length - l.length, l₂.length - l.length, _, _⟩; symmetry,
  {
    sorry
  },
  {
    sorry
  },
end

lemma sum_append_repeat_zero {l : list ℕ} {n : ℕ} :
  (l ++ list.repeat 0 n).sum = l.sum :=
by { rw [list.sum_append, list.sum_repeat], refl }

lemma sum_eq_sum_of_foldr_eq_foldr {l₁ l₂ : list ℕ}
  (h : l₁.foldr (λ (a b : ℕ), a + b * 10) 0 = l₂.foldr (λ (a b : ℕ), a + b * 10) 0) :
  l₁.sum = l₂.sum :=
begin
  obtain ⟨l, n₁, n₂, rfl, rfl⟩ := exi_eq_append_zeros_of_foldr_eq_foldr h,
  simp_rw sum_append_repeat_zero,
end

lemma sum_eq_sum_of_foldl_eq_foldr {l₁ l₂ : list ℕ}
  (h : l₁.foldl (λ (a b : ℕ), a * 10 + b) 0 = l₂.foldr (λ (a b : ℕ), a + b * 10) 0) :
  l₁.sum = l₂.sum :=
begin
  rw ←list.sum_reverse l₁,
  rw ←list.foldr_reverse _ _ l₁ at h,
  rename l₁ l,
  revert h,
  generalize : l.reverse = l₁,
  intro h,
  clear l,
  replace h : list.foldr (λ a b, a + b * 10) 0 l₁ = list.foldr (λ a b, a + b * 10) 0 l₂,
  { convert h; ext a b; rw add_comm },
  exact sum_eq_sum_of_foldr_eq_foldr h,
end

lemma sum_digits_def {n : ℕ} :
  sum_digits n = (get_some (λ (l : list ℕ), l.foldr (λ (a b : ℕ), a + b * 10) 0 = n)).sum :=
begin
  apply get_some_eq_get_some_of_exists_iff,
  { split; rintro ⟨l, rfl⟩; use l.reverse;
    { rw list.foldl_reverse <|> rw list.foldr_reverse, simp_rw add_comm }},
  { rintro h₁ h₂, have h₃ := h₁.some_spec, have h₄ := h₂.some_spec,
    have h₅ : list.foldl (λ (a b : ℕ), a * 10 + b) 0 h₁.some =
      list.foldr (λ (a b : ℕ), a + b * 10) 0 h₂.some := by rw [h₃, h₄],
    exact sum_eq_sum_of_foldl_eq_foldr h₅ },
end

lemma sum_eq_zero_of_foldr_eq_zero {l : list ℕ}
  (h : l.foldr (λ (a b : ℕ), a + b * 10) 0 = 0) :
  l.sum = 0 :=
begin
  induction' l with hd l ih,
  { refl },
  { rw [list.foldr_cons, add_eq_zero_iff] at h, rcases h with ⟨rfl, h⟩,
    apply ih, rw mul_eq_zero at h, cases h,
    { exact h },
    { cases h }},
end

lemma sum_digits_zero : sum_digits 0 = 0 :=
begin
  rw [sum_digits_def, get_some_pos], swap,
  { exact ⟨[], rfl⟩ },
  generalize_proofs h, exact sum_eq_zero_of_foldr_eq_zero h.some_spec,
end

lemma iter_sum_digits_zero {n : ℕ} : (sum_digits^[n]) 0 = 0 :=
begin
  induction' n,
  { refl },
  { rw [function.iterate_succ_apply', ih, sum_digits_zero] },
end

lemma digital_root_zero : digital_root 0 = 0 :=
begin
  rw [digital_root, repeated, get_some_pos], swap,
  { exact ⟨0, 0, rfl, sum_digits_zero⟩ },
  generalize_proofs h₁, obtain ⟨n, h₂, h₃⟩ := h₁.some_spec,
  rw iter_sum_digits_zero at h₂, exact h₂.symm,
end

-- #exit

lemma digital_root_eq {n : ℕ} :
  digital_root n = if n = 0 then 0 else if n.mod 9 = 0 then 9 else n.mod 9 :=
begin
  split_ifs with h h₁,
  sorry { cases h, exact digital_root_zero },
  {
    sorry
  },
  {
    sorry
  },
end