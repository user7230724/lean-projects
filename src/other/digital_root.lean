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

def is_digit (n : ℕ) : Prop := n ≤ 9

def is_digit_list (l : list ℕ) : Prop := ∀ (n ∈ l), is_digit n

def get_digits (n : ℕ) : list ℕ :=
get_some (λ (l : list ℕ), is_digit_list l ∧ l.foldl (λ (a b : ℕ), a * 10 + b) 0 = n)

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
| (0::l) := trim_start l
| l := l

def trim_end : list ℕ → list ℕ :=
reversed trim_start

lemma list_reverse_snoc {α : Type} {l : list α} {x : α} :
  (l ++ [x]).reverse = x :: l.reverse := list.reverse_append _ _

lemma trim_start_zero_cons {l : list ℕ} : trim_start (0 :: l) = trim_start l := rfl

lemma trim_start_succ_cons {l : list ℕ} {n : ℕ} :
  trim_start (n.succ :: l) = n.succ :: l := rfl

lemma trim_end_snoc_zero {l : list ℕ} : trim_end (l ++ [0]) = trim_end l :=
by { rw [trim_end, reversed, list_reverse_snoc, trim_start_zero_cons], refl }

lemma list_length_snoc {α : Type} {l : list α} {x : α} :
  (l ++ [x]).length = l.length + 1 := list.length_append _ _

lemma trim_end_snoc_succ {l : list ℕ} {n : ℕ} :
  trim_end (l ++ [n.succ]) = l ++ [n.succ] :=
by rw [trim_end, reversed, list_reverse_snoc, trim_start_succ_cons,
  list.reverse_cons, list.reverse_reverse]

lemma length_trim_end_le {l : list ℕ} : (trim_end l).length ≤ l.length :=
begin
  induction l using list.reverse_rec_on with l n ih,
  { refl },
  { cases n,
    { rw [trim_end_snoc_zero, list_length_snoc],
      exact nat.le_succ_of_le ih },
    { rw [trim_end_snoc_succ] }},
end

lemma list_repeat_succ_snoc {α : Type} {x : α} {n : ℕ} :
  list.repeat x n.succ = list.repeat x n ++ [x] :=
by { rw list.repeat_add x n 1, refl }

lemma trim_end_append_repeat_zero {l : list ℕ} :
  trim_end l ++ list.repeat 0 (l.length - (trim_end l).length) = l :=
begin
  induction l using list.reverse_rec_on with l n ih,
  { refl },
  { cases n,
    { rw [trim_end_snoc_zero, list_length_snoc, nat.sub_add_comm length_trim_end_le,
        list_repeat_succ_snoc, ←list.append_assoc, ih] },
    { rw [trim_end_snoc_succ, list_length_snoc, nat.sub_self,
      list.repeat, list.append_nil] }},
end

lemma is_digit_list_nil : is_digit_list [] :=
by { rintro x h, cases h }

lemma is_digit_list_cons {l : list ℕ} {n : ℕ} :
  is_digit_list (n :: l) ↔ is_digit n ∧ is_digit_list l :=
begin
  split; intro h,
  { split,
    { exact h _ (list.mem_cons_self _ _) },
    { rintro m h₁, exact h m (list.mem_cons_of_mem _ h₁) }},
  { cases h with h₁ h₂, rintro m h₃, rw list.mem_cons_iff at h₃, cases h₃,
    { subst m, exact h₁ },
    { exact h₂ m h₃ }},
end

lemma is_digit_list_append {l₁ l₂ : list ℕ} :
  is_digit_list (l₁ ++ l₂) ↔ is_digit_list l₁ ∧ is_digit_list l₂ :=
begin
  split; intro h,
  { split; rintro n h₁; apply h n,
    { exact list.mem_append_left _ h₁ },
    { exact list.mem_append_right _ h₁ }},
  { cases h with h₁ h₂, rintro n h₃, rw list.mem_append_eq at h₃, cases h₃,
    { exact h₁ _ h₃ },
    { exact h₂ _ h₃ }},
end

lemma is_digit_list_singleton {n : ℕ} : is_digit_list [n] ↔ is_digit n :=
begin
  split; intro h,
  { exact h _ (list.mem_singleton_self _) },
  { rintro m h₁, rw list.mem_singleton at h₁, subst m, exact h },
end

lemma is_digit_list_snoc {l : list ℕ} {n : ℕ} :
  is_digit_list (l ++ [n]) ↔ is_digit_list l ∧ is_digit n :=
by rw [is_digit_list_append, is_digit_list_singleton]

lemma is_digit_list_reverse {l : list ℕ} : is_digit_list l.reverse ↔ is_digit_list l :=
begin
  induction l with n l ih,
  { refl },
  { rw [list.reverse_cons, is_digit_list_snoc, is_digit_list_cons], tauto },
end

lemma exi_eq_append_zeros_of_foldr_eq_foldr {l₁ l₂ : list ℕ}
  (h₁ : is_digit_list l₁) (h₂ : is_digit_list l₂)
  (h₃ : l₁.foldr (λ (a b : ℕ), a + b * 10) 0 = l₂.foldr (λ (a b : ℕ), a + b * 10) 0) :
  ∃ (l : list ℕ) (n₁ n₂ : ℕ), l₁ = l ++ list.repeat 0 n₁ ∧ l₂ = l ++ list.repeat 0 n₂ :=
begin
  let l := trim_end l₁,
  use [l, l₁.length - l.length, l₂.length - l.length, trim_end_append_repeat_zero.symm],
  symmetry,
  sorry
end

-- #exit

lemma sum_append_repeat_zero {l : list ℕ} {n : ℕ} :
  (l ++ list.repeat 0 n).sum = l.sum :=
by { rw [list.sum_append, list.sum_repeat], refl }

lemma sum_eq_sum_of_foldr_eq_foldr {l₁ l₂ : list ℕ}
  (h₁ : is_digit_list l₁) (h₂ : is_digit_list l₂)
  (h₃ : l₁.foldr (λ (a b : ℕ), a + b * 10) 0 = l₂.foldr (λ (a b : ℕ), a + b * 10) 0) :
  l₁.sum = l₂.sum :=
begin
  obtain ⟨l, n₁, n₂, rfl, rfl⟩ := exi_eq_append_zeros_of_foldr_eq_foldr h₁ h₂ h₃,
  simp_rw sum_append_repeat_zero,
end

lemma sum_eq_sum_of_foldl_eq_foldr {l₁ l₂ : list ℕ}
  (h₁ : is_digit_list l₁) (h₂ : is_digit_list l₂)
  (h₃ : l₁.foldl (λ (a b : ℕ), a * 10 + b) 0 = l₂.foldr (λ (a b : ℕ), a + b * 10) 0) :
  l₁.sum = l₂.sum :=
begin
  rw ←list.sum_reverse l₁,
  rw ←list.foldr_reverse _ _ l₁ at h₃,
  rename l₁ l,
  rw ←is_digit_list_reverse at h₁,
  revert h₁ h₃,
  generalize : l.reverse = l₁,
  rintro h₁ h₃,
  clear l,
  replace h₃ : list.foldr (λ a b, a + b * 10) 0 l₁ = list.foldr (λ a b, a + b * 10) 0 l₂,
  { convert h₃; ext a b; rw add_comm },
  exact sum_eq_sum_of_foldr_eq_foldr h₁ h₂ h₃,
end

lemma sum_digits_def {n : ℕ} :
  sum_digits n = (get_some (λ (l : list ℕ), is_digit_list l ∧
    l.foldr (λ (a b : ℕ), a + b * 10) 0 = n)).sum :=
begin
  sorry
  -- apply get_some_eq_get_some_of_exists_iff,
  -- { split; rintro ⟨l, rfl⟩; use l.reverse;
  --   { rw list.foldl_reverse <|> rw list.foldr_reverse, simp_rw add_comm }},
  -- { rintro h₁ h₂, have h₃ := h₁.some_spec, have h₄ := h₂.some_spec,
  --   have h₅ : list.foldl (λ (a b : ℕ), a * 10 + b) 0 h₁.some =
  --     list.foldr (λ (a b : ℕ), a + b * 10) 0 h₂.some := by rw [h₃, h₄],
  --   exact sum_eq_sum_of_foldl_eq_foldr h₅ },
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
  { exact ⟨[], is_digit_list_nil, rfl⟩ },
  generalize_proofs h, exact sum_eq_zero_of_foldr_eq_zero h.some_spec.2,
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

def mod' (n : ℕ) : ℕ := if n.mod 9 = 0 then 9 else n.mod 9

-- #exit

lemma digital_root_eq {n : ℕ} :
  digital_root n = if n = 0 then 0 else if n.mod 9 = 0 then 9 else n.mod 9 :=
begin
  rw ←mod',
  split_ifs with h h₁,
  sorry { cases h, exact digital_root_zero },
  {
    sorry
  },
end