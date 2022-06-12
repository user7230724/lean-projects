import tactic
import tactic.induction
import logic.function.iterate
import data.list.basic

noncomputable theory
open_locale classical

def get_some {α : Type} [inhabited α] (P : α → Prop) : α :=
if h : ∃ (x : α), P x then h.some else default

def fixed {α : Type} [inhabited α] (f : α → α) (z : α) : α :=
get_some (λ (x : α), ∃ (n : ℕ), (f^[n]) z = x ∧ (f^[n + 1]) z = x)

def all {α : Type} (P : α → Prop) (l : list α) : Prop := l.all (λ (x : α), P x)

def is_digit (n : ℕ) : Prop := n ≤ 9

def is_digit_list (l : list ℕ) : Prop := all is_digit l

def get_digits (n : ℕ) : list ℕ :=
get_some (λ (l : list ℕ), is_digit_list l ∧ l.foldl (λ (a b : ℕ), a * 10 + b) 0 = n)

def sum_digits (n : ℕ) : ℕ := (get_digits n).sum

def digital_root (n : ℕ) : ℕ := fixed sum_digits n

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

instance {n : ℕ} : decidable (is_digit n) :=
by { rw is_digit, apply_instance }

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

lemma all_nil {α : Type} {P : α → Prop} : all P [] := by simp [all]

lemma all_cons {α : Type} {P : α → Prop} {l : list α} {x : α} :
  all P (x :: l) ↔ P x ∧ all P l := by simp [all]

lemma all_iff {α : Type} {P : α → Prop} {l : list α} : all P l ↔ ∀ (x ∈ l), P x :=
begin
  induction l with x l ih,
  { simp [all_nil] },
  { simp [all_cons, ih] },
end

lemma all_append {α : Type} {P : α → Prop} {l₁ l₂ : list α} :
  all P (l₁ ++ l₂) ↔ all P l₁ ∧ all P l₂ :=
begin
  simp_rw all_iff, split; intro h,
  { split; rintro n h₁; apply h n,
    { exact list.mem_append_left _ h₁ },
    { exact list.mem_append_right _ h₁ }},
  { cases h with h₁ h₂, rintro n h₃, rw list.mem_append_eq at h₃, cases h₃,
    { exact h₁ _ h₃ },
    { exact h₂ _ h₃ }},
end

lemma all_singleton {α : Type} {P : α → Prop} {x : α} : all P [x] ↔ P x :=
begin
  simp_rw all_iff, split; intro h,
  { exact h _ (list.mem_singleton_self _) },
  { rintro m h₁, rw list.mem_singleton at h₁, subst m, exact h },
end

lemma all_snoc {α : Type} {P : α → Prop} {l : list α} {x : α} :
  all P (l ++ [x]) ↔ all P l ∧ P x := by rw [all_append, all_singleton]

lemma all_reverse {α : Type} {P : α → Prop} {l : list α} : all P l.reverse ↔ all P l :=
begin
  induction l with n l ih,
  { refl },
  { rw [list.reverse_cons, all_snoc, all_cons], tauto },
end

lemma is_digit_of_is_digit_add {d₁ d₂ : ℕ} (h : is_digit (d₁ + d₂)) :
  is_digit d₁ ∧ is_digit d₂ := ⟨nat.le_of_add_le_left h, nat.le_of_add_le_right h⟩

lemma not_is_digit_add_10 {n : ℕ} : ¬is_digit (n + 10) := dec_trivial

lemma is_digit_mul_10 {n : ℕ} : is_digit (n * 10) ↔ n = 0 :=
begin
  split; intro h,
  { cases n,
    { refl },
    { revert h, rw nat.succ_mul, dec_trivial }},
  { subst n, dec_trivial },
end

lemma sum_eq_zero_of_foldr_eq_zero {l : list ℕ}
  (h : l.foldr (λ (a b : ℕ), a + b * 10) 0 = 0) : l.sum = 0 :=
begin
  induction' l with hd l ih,
  { refl },
  { rw [list.foldr_cons, add_eq_zero_iff] at h, rcases h with ⟨rfl, h⟩,
    apply ih, rw mul_eq_zero at h, cases h,
    { exact h },
    { cases h }},
end

lemma sum_eq_of_foldr_eq_digit {l : list ℕ} {d : ℕ}
  (h₁ : is_digit_list l) (h₂ : is_digit d)
  (h₃ : l.foldr (λ (a b : ℕ), a + b * 10) 0 = d) : l.sum = d :=
begin
  cases l with d₁ l,
  { exact h₃ },
  { rw list.sum_cons, rw list.foldr_cons at h₃, rw [is_digit_list, all_cons] at h₁,
    cases h₁ with h₁ h₄, subst d, congr, have h₃ := (is_digit_of_is_digit_add h₂).2,
    rw is_digit_mul_10 at h₃, rw h₃, exact sum_eq_zero_of_foldr_eq_zero h₃ },
end

lemma is_digit_succ {n : ℕ} : is_digit n.succ ↔ n < 9 :=
begin
  rw [is_digit, le_iff_lt_or_eq], split; intro h,
  { cases h,
    { exact nat.lt_of_succ_lt h },
    { cases h, dec_trivial }},
  { rwa [←nat.succ_le_iff, le_iff_lt_or_eq] at h },
end

lemma nat_exi_mul (x y : ℕ) :
  ∃ (a b : ℕ), a = x / y ∧ b = x % y ∧ x = a * y + b :=
by { simp_rw mul_comm, exact ⟨_, _, rfl, rfl, (nat.div_add_mod _ _).symm⟩ }

lemma is_digit_mod_10 {n : ℕ} : is_digit (n % 10) :=
by { rw [is_digit, ←nat.lt_succ_iff], apply nat.mod_lt, dec_trivial }

lemma digit_ind {P : ℕ → Prop} {n : ℕ}
  (h₁ : P 0) (h₂ : ∀ (d n : ℕ), is_digit d → P n → P (d + n * 10)) : P n :=
begin
  induction n using nat.strong_induction_on with n ih, dsimp at ih,
  obtain ⟨a, b, ha, hb, h₃⟩ := nat_exi_mul n 10, rw [h₃, add_comm], apply h₂,
  { rw hb, exact is_digit_mod_10 },
  { rw ha, cases n,
    { exact h₁ },
    { apply ih, apply nat.div_lt_self; dec_trivial }},
end

def all_zeros (l : list ℕ) : Prop := all (λ (n : ℕ), n = 0) l

lemma foldr_eq_zero_iff {l : list ℕ} :
  l.foldr (λ (a b : ℕ), a + b * 10) 0 = 0 ↔ all_zeros l :=
begin
  induction l with x l ih,
  { simp [all_zeros, all_nil] },
  { rw [list.foldr_cons, all_zeros, all_cons, ←all_zeros, ←ih,
    add_eq_zero_iff, mul_eq_zero], tauto },
end

lemma trim_end_nil : trim_end [] = [] := rfl

lemma trim_end_eq_nil_iff {l : list ℕ} : trim_end l = [] ↔ all_zeros l :=
begin
  induction l using list.reverse_rec_on with l n ih,
  { simp [trim_end_nil, all_zeros, all_nil] },
  { cases n,
    { simp [trim_end_snoc_zero, ih, all_zeros, all_snoc] },
    { simp [trim_end_snoc_succ, all_zeros, all_snoc] }},
end

lemma left_lt_of_add_lt {a b c : ℕ} (h : a + b < c) : a < c := buffer.lt_aux_1 h

lemma right_lt_of_add_lt {a b c : ℕ} (h : a + b < c) : b < c :=
by { rw add_comm at h, exact left_lt_of_add_lt h }

lemma lt_of_add_lt {a b c : ℕ} (h : a + b < c) : a < c ∧ b < c :=
⟨left_lt_of_add_lt h, right_lt_of_add_lt h⟩

lemma not_add_self_lt_self {a b : ℕ} : ¬a + b < b :=
by { intro h, cases lt_irrefl _ (right_lt_of_add_lt h) }

lemma eq_zero_of_mul_lt_self {a b : ℕ} (h : a * b < a) : b = 0 :=
begin
  cases b,
  { refl },
  { rw nat.mul_succ at h, cases not_add_self_lt_self h },
end

lemma add_mul_eq_add_mul_iff {k d₁ d₂ a b : ℕ} (h₁ : d₁ < k) (h₂ : d₂ < k) :
  d₁ + a * k = d₂ + b * k ↔ d₁ = d₂ ∧ a = b :=
begin
  split; intro h,
  { induction a with a ih generalizing b,
    { rw [zero_mul, add_zero] at h, subst d₁, have h₃ := right_lt_of_add_lt h₁,
      rw mul_comm at h₃, replace h₃ := eq_zero_of_mul_lt_self h₃, subst b,
      rw zero_mul, exact ⟨rfl, rfl⟩ },
    { rw [nat.succ_mul, ←add_assoc] at h, cases b,
      { rw [zero_mul, add_zero] at h, subst d₂, cases not_add_self_lt_self h₂ },
      { rw [nat.succ_mul, ←add_assoc, add_left_inj] at h,
        rw nat.succ_inj', exact ih h }}},
  { rw [h.1, h.2] },
end

lemma digit_lt_10 {d : ℕ} (h : is_digit d) : d < 10 := by rwa nat.lt_succ_iff

lemma digit_add_mul_10_eq_digit_add_mul_10_iff {d₁ d₂ a b : ℕ}
  (h₁ : is_digit d₁) (h₂ : is_digit d₂) :
  d₁ + a * 10 = d₂ + b * 10 ↔ d₁ = d₂ ∧ a = b :=
by { rw add_mul_eq_add_mul_iff; apply digit_lt_10; assumption }

lemma trim_end_cons {l : list ℕ} {n : ℕ} :
  trim_end (n :: l) = if all_zeros l then trim_end [n] else n :: trim_end l :=
begin
  split_ifs,
  { induction l using list.reverse_rec_on with l m ih,
    { refl },
    { rw [all_zeros, all_snoc, ←all_zeros] at h, rcases h with ⟨h, rfl⟩,
      specialize ih h, rwa [←list.cons_append, trim_end_snoc_zero] }},
  { induction l using list.reverse_rec_on with l m ih,
    { cases h all_nil },
    { rw ←list.cons_append,
      rw [all_zeros, all_snoc, ←all_zeros, not_and_distrib] at h, cases m,
      { simp_rw trim_end_snoc_zero, cases h,
        { exact ih h },
        { cases h rfl }},
      { simp_rw [trim_end_snoc_succ, list.cons_append], use rfl }}},
end

lemma trim_end_all_zeros {l : list ℕ} (h : all_zeros l) : trim_end l = [] :=
by rwa trim_end_eq_nil_iff

lemma trim_end_singleton {n : ℕ} : trim_end [n] = if n = 0 then [] else [n] :=
begin
  split_ifs,
  { subst n, refl },
  { change [n] with [] ++ [n], cases n,
    { cases h rfl },
    { rw trim_end_snoc_succ }},
end

-- #exit

lemma trim_end_same_cons_eq_iff_aux {l₁ l₂ : list ℕ} {n : ℕ}
  (h₁ : all_zeros l₁) (h₂ : ¬all_zeros l₂) :
  trim_end [n] = n :: trim_end l₂ ↔ trim_end l₁ = trim_end l₂ :=
begin
  rw trim_end_all_zeros h₁, split; intro h,
  { rw trim_end_singleton at h, split_ifs at h with h₃,
    { cases h },
    { exact h.2 }},
  { symmetry' at h, rw trim_end_eq_nil_iff at h, contradiction }
end

lemma trim_end_same_cons_eq_iff {l₁ l₂ : list ℕ} {n : ℕ} :
  trim_end (n :: l₁) = trim_end (n :: l₂) ↔ trim_end l₁ = trim_end l₂ :=
begin
  nth_rewrite 0 trim_end_cons, nth_rewrite 1 trim_end_cons, split_ifs with h₁ h₂ h₂,
  { simp [trim_end_all_zeros h₁, trim_end_all_zeros h₂] },
  { exact trim_end_same_cons_eq_iff_aux h₁ h₂ },
  { have := @trim_end_same_cons_eq_iff_aux _ _ n h₂ h₁, tauto },
  { simp }
end

lemma trim_end_eq_trim_end_of_foldr_eq_foldr {l₁ l₂ : list ℕ}
  (h₁ : is_digit_list l₁) (h₂ : is_digit_list l₂)
  (h₃ : l₁.foldr (λ (a b : ℕ), a + b * 10) 0 = l₂.foldr (λ (a b : ℕ), a + b * 10) 0) :
  trim_end l₁ = trim_end l₂ :=
begin
  induction l₁ with n l₁ ih generalizing l₂,
  { rw trim_end_nil, symmetry' at h₃ ⊢, change _ = 0 at h₃,
    rw foldr_eq_zero_iff at h₃, rwa trim_end_eq_nil_iff },
  { rw [is_digit_list, all_cons, ←is_digit_list] at h₁,
    cases h₁ with h₁ h₄, specialize @ih h₄, cases l₂ with m l₂,
    { change _ = 0 at h₃,
      rw [list.foldr_cons, add_eq_zero_iff, mul_eq_zero, foldr_eq_zero_iff] at h₃,
      rcases h₃ with ⟨rfl, h₃⟩, rw [trim_end_nil, trim_end_eq_nil_iff, all_zeros, all_cons],
      use rfl, cases h₃,
      { exact h₃ },
      { cases h₃ }},
    { rw [is_digit_list, all_cons, ←is_digit_list] at h₂, cases h₂ with h₂ h₅,
      simp_rw [list.foldr_cons, digit_add_mul_10_eq_digit_add_mul_10_iff h₁ h₂] at h₃,
      rcases h₃ with ⟨rfl, h₃⟩, rw trim_end_same_cons_eq_iff, exact ih h₅ h₃ }},
end

lemma exi_eq_append_zeros_of_foldr_eq_foldr {l₁ l₂ : list ℕ}
  (h₁ : is_digit_list l₁) (h₂ : is_digit_list l₂)
  (h₃ : l₁.foldr (λ (a b : ℕ), a + b * 10) 0 = l₂.foldr (λ (a b : ℕ), a + b * 10) 0) :
  ∃ (l : list ℕ) (n₁ n₂ : ℕ), l₁ = l ++ list.repeat 0 n₁ ∧ l₂ = l ++ list.repeat 0 n₂ :=
begin
  use [trim_end l₁, l₁.length - (trim_end l₁).length, l₂.length - (trim_end l₁).length,
    trim_end_append_repeat_zero.symm], symmetry,
  rw [(_ : trim_end l₁ = trim_end l₂), trim_end_append_repeat_zero],
  exact trim_end_eq_trim_end_of_foldr_eq_foldr h₁ h₂ h₃,
end

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
  rw [is_digit_list, ←all_reverse, ←is_digit_list] at h₁,
  revert h₁ h₃,
  generalize : l.reverse = l₁,
  rintro h₁ h₃,
  clear l,
  replace h₃ : list.foldr (λ a b, a + b * 10) 0 l₁ = list.foldr (λ a b, a + b * 10) 0 l₂,
  { convert h₃; ext a b; rw add_comm },
  exact sum_eq_sum_of_foldr_eq_foldr h₁ h₂ h₃,
end

lemma exi_foldl_iff_exi_foldr {n : ℕ} :
  (∃ (l : list ℕ), is_digit_list l ∧ l.foldl (λ (a b : ℕ), a * 10 + b) 0 = n) ↔
  (∃ (l : list ℕ), is_digit_list l ∧ l.foldr (λ (a b : ℕ), a + b * 10) 0 = n) :=
begin
  split; rintro ⟨l, hl, rfl⟩; use l.reverse;
  { rw list.foldl_reverse <|> rw list.foldr_reverse,
    simp_rw add_comm, rw [is_digit_list, all_reverse, ←is_digit_list], use hl },
end

lemma sum_digits_eq_get_some {n : ℕ} :
  sum_digits n = (get_some (λ (l : list ℕ), is_digit_list l ∧
    l.foldr (λ (a b : ℕ), a + b * 10) 0 = n)).sum :=
begin
  apply get_some_eq_get_some_of_exists_iff exi_foldl_iff_exi_foldr,
  rintro h₁ h₂, have h₃ := h₁.some_spec, have h₄ := h₂.some_spec,
  have h₅ : list.foldl (λ (a b : ℕ), a * 10 + b) 0 h₁.some =
    list.foldr (λ (a b : ℕ), a + b * 10) 0 h₂.some := by rw [h₃.2, h₄.2],
  exact sum_eq_sum_of_foldl_eq_foldr h₃.1 h₄.1 h₅,
end

lemma sum_digits_zero : sum_digits 0 = 0 :=
begin
  rw [sum_digits_eq_get_some, get_some_pos], swap,
  { exact ⟨[], all_nil, rfl⟩ },
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
  rw [digital_root, fixed, get_some_pos], swap,
  { exact ⟨0, 0, rfl, sum_digits_zero⟩ },
  generalize_proofs h₁, obtain ⟨n, h₂, h₃⟩ := h₁.some_spec,
  rw iter_sum_digits_zero at h₂, exact h₂.symm,
end

def modp (n k : ℕ) : ℕ := if n % k = 0 then k else n % k

lemma modp_digit_of_pos {d : ℕ} (h₁ : is_digit d) (h₂ : 0 < d) : modp d 9 = d :=
begin
  rw modp, split_ifs,
  { rw [is_digit, le_iff_lt_or_eq] at h₁, cases h₁,
    { rw nat.mod_eq_of_lt h₁ at h, rw h at h₂, cases h₂ },
    { exact h₁.symm }},
  { rw [is_digit, le_iff_lt_or_eq] at h₁, cases h₁,
    { exact nat.mod_eq_of_lt h₁ },
    { subst d, contradiction }},
end

lemma sum_digits_digit {d : ℕ} (h : is_digit d) : sum_digits d = d :=
begin
  rw [sum_digits_eq_get_some, get_some_pos], swap,
  { exact ⟨[d], all_singleton.mpr h, rfl⟩ },
  generalize_proofs h₁, obtain ⟨h₂, h₃⟩ := h₁.some_spec,
  exact sum_eq_of_foldr_eq_digit h₂ h h₃,
end

lemma iterate_eq_self {α : Type} {f : α → α} {x : α} {n : ℕ}
  (h : f x = x) : (f^[n] x) = x :=
begin
  induction n with n ih,
  { refl },
  { rw [function.iterate_succ_apply', ih, h] },
end

lemma fixed_eq_self_of {α : Type} [inhabited α] {f : α → α} {x : α}
  (h : f x = x) : fixed f x = x :=
begin
  rw [fixed, get_some_pos], swap,
  { exact ⟨x, 0, rfl, h⟩ },
  generalize_proofs h₁, obtain ⟨n, h₂, h₃⟩ := h₁.some_spec,
  rw [←h₂, iterate_eq_self h],
end

lemma digital_root_digit_eq_self {d : ℕ} (h : is_digit d) :
  digital_root d = d := fixed_eq_self_of (sum_digits_digit h)

lemma is_digit_modp_9 {n : ℕ} : is_digit (modp n 9) :=
begin
  rw [is_digit, modp], split_ifs,
  { refl },
  { apply le_of_lt, apply nat.mod_lt, dec_trivial },
end

lemma is_digit_digit_add_digit_sub {d₁ d₂ n : ℕ} (h₁ : is_digit d₁) (h₂ : is_digit d₂)
  (h₃ : 9 ≤ n) : is_digit (d₁ + d₂ - n) :=
begin
  rw is_digit at h₁ h₂ ⊢,
  have h₄ := (add_le_add h₁ h₂).trans (add_le_add (le_refl _) h₃),
  rwa tsub_le_iff_right,
end

lemma exi_digit_add_10_of_not_is_digit_add {d₁ d₂ : ℕ}
  (h₁ : is_digit d₁) (h₂ : is_digit d₂) (h₃ : ¬is_digit (d₁ + d₂)) :
  ∃ (d : ℕ), is_digit d ∧ d₁ + d₂ = d + 10 :=
begin
  refine ⟨d₁ + d₂ - 10, _, _⟩,
  { apply is_digit_digit_add_digit_sub h₁ h₂, dec_trivial },
  { rw [is_digit, not_le] at h₃, obtain ⟨k, h₄⟩ := nat.exists_eq_add_of_lt h₃,
    rw h₄, refine (nat.sub_eq_iff_eq_add _).mp rfl, rw add_right_comm, exact le_self_add },
end

lemma exi_digit_add_9_of_not_is_digit_add {d₁ d₂ : ℕ}
  (h₁ : is_digit d₁) (h₂ : is_digit d₂) (h₃ : ¬is_digit (d₁ + d₂)) :
  ∃ (d : ℕ), is_digit d ∧ d₁ + d₂ = d + 9 :=
begin
  refine ⟨d₁ + d₂ - 9, _, _⟩,
  { apply is_digit_digit_add_digit_sub h₁ h₂, dec_trivial },
  { rw [is_digit, not_le] at h₃, obtain ⟨k, h₄⟩ := nat.exists_eq_add_of_lt h₃,
    rw h₄, refine (nat.sub_eq_iff_eq_add _).mp rfl, apply nat.le_succ_of_le,
    exact le_self_add },
end

lemma is_digit_of_is_digit_succ {d : ℕ} (h : is_digit d.succ) : is_digit d :=
(@is_digit_of_is_digit_add d 1 h).1

lemma sum_eq_of_foldr_eq_digit_add_10 {l : list ℕ} {d : ℕ}
  (h₁ : is_digit_list l) (h₂ : is_digit d)
  (h₃ : l.foldr (λ (a b : ℕ), a + b * 10) 0 = d + 10) : l.sum = d.succ :=
begin
  cases l with d₁ l,
  { cases h₃ },
  { rw list.foldr_cons at h₃, rw [is_digit_list, all_cons, ←is_digit_list] at h₁,
    cases h₁ with h₁ h₄, nth_rewrite 1 ←one_mul 10 at h₃,
    rw digit_add_mul_10_eq_digit_add_mul_10_iff h₁ h₂ at h₃, rcases h₃ with ⟨rfl, h₃⟩,
    rw [list.sum_cons, sum_eq_of_foldr_eq_digit h₄ dec_trivial h₃] },
end

lemma sum_digits_pos_digit_add_9 {d : ℕ} (h₁ : is_digit d) (h₂ : 0 < d) :
  sum_digits (d + 9) = d :=
begin
  cases d,
  { cases h₂ },
  { rw [sum_digits_eq_get_some, get_some_pos], swap,
    { refine ⟨[d, 1], _, _⟩,
      { simp_rw [is_digit_list, all_cons, all_nil],
        exact ⟨is_digit_of_is_digit_succ h₁, dec_trivial, trivial⟩ },
      { refl }},
    generalize_proofs h₃, obtain ⟨h₄, h₅⟩ := h₃.some_spec, change _ = d + 10 at h₅,
    exact sum_eq_of_foldr_eq_digit_add_10 h₄ (is_digit_of_is_digit_succ h₁) h₅ },
end

lemma pos_left_of_not_is_digit_digit_add_digit {d₁ d₂ : ℕ}
  (h₁ : is_digit d₁) (h₂ : is_digit d₂) (h₃ : ¬is_digit (d₁ + d₂)) : 0 < d₁ :=
by { rw is_digit at h₁ h₂ h₃, linarith }

lemma pos_right_of_not_is_digit_digit_add_digit {d₁ d₂ : ℕ}
  (h₁ : is_digit d₁) (h₂ : is_digit d₂) (h₃ : ¬is_digit (d₁ + d₂)) : 0 < d₂ :=
by { rw add_comm at h₃, exact pos_left_of_not_is_digit_digit_add_digit h₂ h₁ h₃ }

lemma sum_digits_digit_add_digit {d₁ d₂ : ℕ} (h₁ : is_digit d₁) (h₂ : is_digit d₂) :
  sum_digits (d₁ + d₂) = if d₁ + d₂ ≤ 9 then d₁ + d₂ else d₁ + d₂ - 9 :=
begin
  split_ifs,
  { exact sum_digits_digit h },
  { obtain ⟨d, h₃, h₄⟩ := exi_digit_add_9_of_not_is_digit_add h₁ h₂ h, have h₅ : 0 < d,
    { rw h₄ at h, push_neg at h, rwa lt_add_iff_pos_left at h },
    rw [h₄, sum_digits_pos_digit_add_9 h₃ h₅], refl },
end

lemma modp_of_le_of_pos {k d : ℕ} (h₁ : 0 < d) (h₂ : d ≤ k) : modp d k = d :=
begin
  rw modp, cases k,
  { rw nat.le_zero_iff at h₂, subst d, refl },
  { split_ifs with h₃,
    { rw le_iff_lt_or_eq at h₂, cases h₂,
      { rw nat.mod_eq_of_lt h₂ at h₃, subst d, cases h₁ },
      { subst d }},
    { rw le_iff_lt_or_eq at h₂, cases h₂,
      { exact nat.mod_eq_of_lt h₂ },
      { subst d, cases h₃ (nat.mod_self _) }}},
end

lemma add_self_mod_eq_zero {a : ℕ} : (a + a) % a = 0 := by simp

lemma modp_add {k a b : ℕ} : modp (a + b) k = modp (modp a k + modp b k) k :=
by { simp_rw modp, split_ifs; simp [*, nat.add_mod] at * }

lemma modp_pos_of_pos {k d : ℕ} (h : 0 < d) : 0 < modp d k :=
begin
  rw modp, split_ifs with h₁,
  { by_contra' h₂, rw nat.le_zero_iff at h₂, subst k,
    rw nat.mod_zero at h₁, subst d, cases h },
  { rwa pos_iff_ne_zero },
end

lemma digital_root_eq_self_of {n : ℕ} (h : sum_digits n = n) :
  digital_root n = n := fixed_eq_self_of h

lemma modp_zero {d : ℕ} : modp d 0 = d :=
begin
  rw [modp, nat.mod_zero], split_ifs,
  { exact h.symm },
  { refl },
end

lemma modp_of_lt {k d : ℕ} (h₁ : 0 < d) (h₂ : d < k) : modp d k = d :=
begin
  rw modp, split_ifs,
  { rw nat.mod_eq_of_lt h₂ at h, subst d, cases h₁ },
  { rw nat.mod_eq_of_lt h₂ },
end

lemma modp_self {k : ℕ} : modp k k = k :=
by { rw [modp, nat.mod_self], refl }

lemma modp_of_le {k d : ℕ} (h₁ : 0 < d) (h₂ : d ≤ k) : modp d k = d :=
begin
  rw le_iff_lt_or_eq at h₂, cases h₂,
  { exact modp_of_lt h₁ h₂ },
  { subst d, rw modp_self },
end

lemma modp_add_self {k d : ℕ} : modp (d + k) k = modp d k :=
begin
  simp_rw modp, split_ifs with h₁ h₂ h₂;
  try { rw nat.add_mod_right at h₁, contradiction },
  { refl },
  { rw nat.add_mod_right },
end

lemma modp_of_gt_of_lt_mul_2 {k d : ℕ} (h₁ : k < d) (h₂ : d < k * 2) : modp d k = d - k :=
begin
  obtain ⟨n, rfl⟩ := nat.exists_eq_add_of_lt h₁, clear h₁,
  replace h₂ : n + 1 < k := by linarith,
  rw [add_rotate k n 1, nat.add_sub_cancel, modp_add_self],
  exact modp_of_lt (nat.succ_pos _) h₂,
end

lemma modp_add_lt {k d₁ d₂ : ℕ} (h₁ : 0 < d₁) (h₂ : 0 < d₂) (h₃ : d₁ < k) (h₄ : d₂ < k) :
  modp (d₁ + d₂) k = if d₁ + d₂ ≤ k then d₁ + d₂ else d₁ + d₂ - k :=
begin
  split_ifs with h₅,
  { exact modp_of_le (add_pos h₁ h₂) h₅ },
  { push_neg at h₅, apply modp_of_gt_of_lt_mul_2 h₅, rw mul_two, exact add_lt_add h₃ h₄ },
end

lemma modp_add_le_aux {k d : ℕ} (h₁ : 0 < d) (h₂ : d < k) :
  modp (d + k) k = if d + k ≤ k then d + k else d + k - k :=
begin
  rw [modp_add_self, if_neg, nat.add_sub_cancel, modp_of_lt h₁ h₂],
  push_neg, exact lt_add_of_pos_left k h₁,
end

lemma modp_add_le {k d₁ d₂ : ℕ} (h₁ : 0 < d₁) (h₂ : 0 < d₂) (h₃ : d₁ ≤ k) (h₄ : d₂ ≤ k) :
  modp (d₁ + d₂) k = if d₁ + d₂ ≤ k then d₁ + d₂ else d₁ + d₂ - k :=
begin
  rw le_iff_lt_or_eq at h₃, cases h₃,
  { rw le_iff_lt_or_eq at h₄, cases h₄,
    { exact modp_add_lt h₁ h₂ h₃ h₄ },
    { subst d₂, exact modp_add_le_aux h₁ h₃ }},
  { subst d₁, rw add_comm k d₂, rw le_iff_lt_or_eq at h₄, cases h₄,
    { exact modp_add_le_aux h₂ h₄ },
    { subst d₂, rw [modp_add_self, modp_self, if_neg, nat.add_sub_cancel],
      push_neg, exact lt_add_of_pos_left k h₁ }},
end

lemma modp_digit_add_digit {d₁ d₂ : ℕ} (h₁ : is_digit d₁) (h₂ : is_digit d₂)
  (h₃ : 0 < d₁) (h₄ : 0 < d₂) :
  modp (d₁ + d₂) 9 = if d₁ + d₂ ≤ 9 then d₁ + d₂ else d₁ + d₂ - 9 :=
modp_add_le h₃ h₄ h₁ h₂

lemma modp_le {k d : ℕ} (h : 0 < k) : modp d k ≤ k :=
begin
  rw modp, split_ifs with h₁,
  { refl },
  { exact le_of_lt (nat.mod_lt _ h) },
end

lemma modp_self_mul {k n : ℕ} : modp (k * n) k = k :=
by { rw modp, split_ifs; simp * at * }

lemma zero_modp {k : ℕ} : modp 0 k = k :=
by { rw modp, split_ifs; simp * at * }

lemma modp_modp {k d : ℕ} : modp (modp d k) k = modp d k :=
begin
  cases k,
  { simp_rw modp_zero },
  { cases d,
    { simp_rw [zero_modp, modp_self] },
    { exact modp_of_le (modp_pos_of_pos (nat.succ_pos _)) (modp_le (nat.succ_pos _)) }},
end

lemma modp_add_self_mul {k d n : ℕ} : modp (d + k * n) k = modp d k :=
by { rw [modp_add, modp_self_mul, modp_add_self, modp_modp] }

lemma modp_digit_add_mul_10 {d n : ℕ} (h : is_digit d) :
  modp (d + n * 10) 9 = modp (d + n) 9 :=
begin
  change 10 with 9 + 1, rw [mul_add, mul_one], cases d,
  { simp_rw zero_add, rw [add_comm, mul_comm, modp_add_self_mul] },
  { rw [modp_add, modp_digit_of_pos h (nat.succ_pos _),
    add_comm (n * 9), mul_comm, modp_add_self_mul, eq_comm,
    modp_add, modp_digit_of_pos h (nat.succ_pos _)] },
end

lemma lt_mul_of_lt {a b c : ℕ} (h₁ : a < b) (h₂ : 0 < c) : a < b * c :=
begin
  cases c,
  { cases h₂ },
  { rw nat.mul_succ, apply nat.lt_add_left, assumption },
end

lemma le_mul_of_le {a b c : ℕ} (h₁ : a ≤ b) (h₂ : 0 < c) : a ≤ b * c :=
begin
  cases c,
  { cases h₂ },
  { rw nat.mul_succ, exact le_add_left h₁},
end

lemma lt_add_left_iff_lt {a b c : ℕ} : c + a < c + b ↔ a < b :=
by apply rel_iff_cov

lemma le_add_left_iff_le {a b c : ℕ} : c + a ≤ c + b ↔ a ≤ b :=
by apply rel_iff_cov

lemma sum_le_foldr {l : list ℕ} : l.sum ≤ l.foldr (λ (a b : ℕ), a + b * 10) 0 :=
begin
  induction l with d l ih,
  { apply zero_le },
  { rw [list.sum_cons, list.foldr_cons, le_add_left_iff_le],
    exact le_mul_of_le ih dec_trivial },
end

lemma add_left_le_self_iff {a b : ℕ} : a + b ≤ b ↔ a = 0 :=
begin
  split; intro h,
  { cases a,
    { refl },
    { rw [nat.succ_add, nat.succ_le_iff] at h,
      cases lt_irrefl _ (right_lt_of_add_lt h) }},
  { subst a, rw zero_add },
end

lemma sum_eq_zero_iff {l : list ℕ} : l.sum = 0 ↔ all_zeros l :=
by { rw [list.sum_eq_zero_iff, all_zeros, all_iff] }

lemma sum_eq_foldr_mul_iff_of_gt_1 {l : list ℕ} {n : ℕ}
  (h₁ : is_digit_list l) (h₂ : 1 < n) :
  l.sum = l.foldr (λ (a b : ℕ), a + b * 10) 0 * n ↔ all_zeros l :=
begin
  split; intro h,
  { have h₃ := @sum_le_foldr l, rw h at h₃,
    obtain ⟨n, rfl⟩ := nat.exists_eq_add_of_lt h₂, clear h₂,
    have h₂ : 1 + n + 1 = n + 2 := by linarith, rw h₂ at *,
    rw [mul_add, mul_two, ←add_assoc, add_left_le_self_iff, add_eq_zero_iff] at h₃,
    rwa [h₃.2, zero_mul, sum_eq_zero_iff] at h },
  { rwa [foldr_eq_zero_iff.mpr h, zero_mul, sum_eq_zero_iff] },
end

lemma is_digit_sum_of_sum_eq_foldr {l : list ℕ} (h₁ : is_digit_list l)
  (h₂ : l.sum = l.foldr (λ (a b : ℕ), a + b * 10) 0) : is_digit l.sum :=
begin
  cases l with d l,
  { dec_trivial },
  { rw [is_digit_list, all_cons, ←is_digit_list] at h₁, cases h₁ with h₁ h₃,
    rw [list.sum_cons, list.foldr_cons, add_right_inj,
    sum_eq_foldr_mul_iff_of_gt_1 h₃ (dec_trivial : 1 < 10)] at h₂,
    rwa [list.sum_cons, sum_eq_zero_iff.mpr h₂] },
end

lemma sum_digits_eq_self_iff_is_digit {n : ℕ} : sum_digits n = n ↔ is_digit n :=
begin
  split; intro h,
  { by_cases h₁ : n = 0,
    { subst n, dec_trivial },
    { rw [sum_digits_eq_get_some, get_some] at h, split_ifs at h with h₁,
      { obtain ⟨h₂, h₃⟩ := h₁.some_spec, revert h h₂ h₃, generalize : h₁.some = l,
        rintro h₁ h₂ h₃, subst n, exact is_digit_sum_of_sum_eq_foldr h₂ h₃.symm },
      { subst n, dec_trivial }}},
  { exact sum_digits_digit h },
end

lemma is_digit_digital_root {n : ℕ} : is_digit (digital_root n) :=
begin
  rw [is_digit, digital_root, fixed, get_some], split_ifs,
  { obtain ⟨k, h₁, h₂⟩ := h.some_spec,
    rwa [function.iterate_succ_apply', h₁, sum_digits_eq_self_iff_is_digit] at h₂ },
  { dec_trivial },
end

lemma exi_sum_digits {n : ℕ} : ∃ (l : list ℕ), is_digit_list l ∧
  l.foldr (λ (a b : ℕ), a + b * 10) 0 = n :=
begin
  induction n using digit_ind with d n h ih,
  { use ([]), split,
    { rw is_digit_list, exact all_nil },
    { refl }},
  { rcases ih with ⟨l, h₁, h₂⟩, use d :: l, split,
    { rw [is_digit_list, all_cons, ←is_digit_list], split; assumption },
    { rw [list.foldr_cons, add_right_inj, h₂] }},
end

lemma sum_digits_digit_add_mul_10 {d n : ℕ} (h : is_digit d) :
  sum_digits (d + n * 10) = d + sum_digits n :=
begin
  rw [sum_digits_eq_get_some, get_some_pos exi_sum_digits], generalize_proofs h₁,
  obtain ⟨h₁, h₂⟩ := h₁.some_spec, revert h₁ h₂, generalize : exi_sum_digits.some = l₂,
  clear h₁, rintro h₁ h₂, rw [sum_digits_eq_get_some, get_some_pos exi_sum_digits],
  generalize_proofs h₁, obtain ⟨h₁, h₂⟩ := h₁.some_spec, revert h₁ h₂,
  generalize : exi_sum_digits.some = l₁, clear h₁, rintro h₃ h₄, cases l₂ with d₂ l₂,
  { change 0 = _ at h₂, symmetry' at h₂, rw [add_eq_zero_iff, mul_eq_zero] at h₂,
    rcases h₂ with ⟨rfl, h₂⟩, clear h h₁, cases h₂,
    { subst n, rw foldr_eq_zero_iff at h₂, rw sum_eq_zero_iff.mpr h₂, refl },
    { cases h₂ }},
  { rw list.foldr_cons at h₂, rw [is_digit_list, all_cons, ←is_digit_list] at h₁,
    cases h₁ with h₁ h₅, rw digit_add_mul_10_eq_digit_add_mul_10_iff h₁ h at h₂,
    rcases h₂ with ⟨rfl, h₂⟩, rw [list.sum_cons, add_right_inj], rw ←h₄ at h₂,
    exact sum_eq_sum_of_foldr_eq_foldr h₅ h₃ h₂ },
end

lemma sum_digits_le {n : ℕ} : sum_digits n ≤ n :=
begin
  induction n using digit_ind with d n h ih,
  { rw sum_digits_zero },
  { rw sum_digits_digit_add_mul_10 h, apply add_le_add_left,
    exact le_trans ih (le_mul_of_le (le_refl _) dec_trivial) },
end

lemma sum_digits_eq_self_of_sum_digits_sum_digits_eq_self {n : ℕ}
  (h : sum_digits (sum_digits n) = n) : sum_digits n = n :=
begin
  apply le_antisymm,
  { exact sum_digits_le },
  { have h₁ := @sum_digits_le (sum_digits n), rwa h at h₁ },
end

lemma iter_le_of_le {f : ℕ → ℕ} {z n : ℕ}
  (h : ∀ (z : ℕ), f z ≤ z) : (f^[n] z) ≤ z :=
begin
  induction n with n ih,
  { refl },
  { rw function.iterate_succ_apply', exact le_trans (h _) ih },
end

lemma iter_le_iter_of_le {f : ℕ → ℕ} {z m n : ℕ}
  (h₁ : ∀ (z : ℕ), f z ≤ z) (h₂ : m ≤ n) : (f^[n] z) ≤ (f^[m] z) :=
begin
  obtain ⟨n, rfl⟩ := nat.exists_eq_add_of_le h₂,
  rw [add_comm, function.iterate_add_apply], exact iter_le_of_le h₁,
end

lemma iter_sum_digits_le_iter_sum_digits_of_le {n k₁ k₂ : ℕ} (h : k₁ ≤ k₂) :
  (sum_digits^[k₂] n) ≤ (sum_digits^[k₁] n) := iter_le_iter_of_le (λ _, sum_digits_le) h

lemma sum_digits_digital_root {n : ℕ} : sum_digits (digital_root n) = digital_root n :=
by { rw sum_digits_eq_self_iff_is_digit, exact is_digit_digital_root }

lemma digital_root_digit {d : ℕ} (h : is_digit d) : digital_root d = d :=
digital_root_eq_self_of (sum_digits_digit h)

lemma digital_root_one : digital_root 1 = 1 := digital_root_digit dec_trivial

lemma is_digit_sum_digits_digit_add_digit {d₁ d₂ : ℕ}
  (h₁ : is_digit d₁) (h₂ : is_digit d₂) : is_digit (sum_digits (d₁ + d₂)) :=
begin
  rw sum_digits_digit_add_digit h₁ h₂, split_ifs,
  { exact h },
  { rw is_digit at *, exact nat.sub_le_sub_right (add_le_add h₁ h₂) 9 },
end

lemma iter_sum_digits_digit {d n : ℕ} (h : is_digit d) : (sum_digits^[n]) d = d :=
function.iterate_fixed (sum_digits_digit h) _

lemma digital_root_digit_add_digit {d₁ d₂ : ℕ} (h₁ : is_digit d₁) (h₂ : is_digit d₂) :
  digital_root (d₁ + d₂) = sum_digits (d₁ + d₂) :=
begin
  rw [digital_root, fixed, get_some_pos], swap,
  { use [sum_digits (d₁ + d₂), 1], split,
    { refl },
    { exact sum_digits_digit (is_digit_sum_digits_digit_add_digit h₁ h₂) }},
  generalize_proofs h₃, obtain ⟨n, -, h₄⟩ := h₃.some_spec,
  symmetry, rwa [function.iterate_succ_apply,
  iter_sum_digits_digit (is_digit_sum_digits_digit_add_digit h₁ h₂)] at h₄,
end

lemma sum_digits_def {n : ℕ} : sum_digits n = n % 10 + sum_digits (n / 10) :=
begin
  obtain ⟨a, b, ha, hb, h⟩ := nat_exi_mul n 10,
  rw [←ha, ←hb, h, add_comm, hb],
  exact sum_digits_digit_add_mul_10 is_digit_mod_10,
end

def converges_to {α : Type} (f : α → α) (z x : α) : Prop :=
∃ (n : ℕ), (f^[n]) z = x ∧ (f^[n + 1]) z = x

def converges {α : Type} (f : α → α) (z : α) : Prop :=
∃ (x : α), converges_to f z x

lemma iter_add {α : Type} {f : α → α} {z : α} {m n : ℕ} :
  (f^[m + n]) z = (f^[n]) ((f^[m]) z) := by rw [add_comm, function.iterate_add_apply]

lemma converges_to_congr_aux {α : Type} {n₂ n₁ : ℕ} {f : α → α} {z x y : α}
  (h₁ : f^[n₁] z = x) (h₂ : f^[n₁ + 1] z = x) (h₃ : f^[n₂] z = y) (h₄ : f^[n₂ + 1] z = y)
  (h₅ : n₁ ≤ n₂) : x = y :=
begin
  obtain ⟨n₂, rfl⟩ := nat.exists_eq_add_of_le h₅, clear h₅, rw add_assoc at h₄,
  simp_rw iter_add at h₂ h₃ h₄, change (f^[1]) with f at h₂ h₄, rw ←h₁ at h₂,
  have h₅ := function.iterate_fixed h₂ n₂, rw [h₃, h₁] at h₅, exact h₅.symm,
end

lemma converges_to_congr {α : Type} {f : α → α} {z x y : α}
  (h₁ : converges_to f z x) (h₂ : converges_to f z y) : x = y :=
begin
  rcases h₂ with ⟨n₂, h₃, h₄⟩, rcases h₁ with ⟨n₁, h₁, h₂⟩, by_cases h₅ : n₁ ≤ n₂,
  { exact converges_to_congr_aux h₁ h₂ h₃ h₄ h₅ },
  { push_neg at h₅, exact (converges_to_congr_aux h₃ h₄ h₁ h₂ (le_of_lt h₅)).symm },
end

lemma fixed_eq_of_converges_to {α : Type} [inhabited α] {f : α → α} {z x : α}
  (h : converges_to f z x) : fixed f z = x :=
begin
  rw [fixed, get_some_pos], swap, { exact ⟨x, h⟩ },
  generalize_proofs h₃, exact converges_to_congr h₃.some_spec h,
end

lemma apply_eq_of_converges_to {α : Type} {f : α → α} {z x : α}
  (h : converges_to f z x) : f x = x :=
by { rcases h with ⟨n, h₁, h₂⟩, rwa [function.iterate_succ_apply', h₁] at h₂ }

lemma apply_fixed_of_converges {α : Type} [inhabited α] {f : α → α} {z : α}
  (h : converges f z) : f (fixed f z) = fixed f z :=
by { cases h with x h, by rw [fixed_eq_of_converges_to h, apply_eq_of_converges_to h] }

lemma iter_apply_comm {α : Type} {f : α → α} {x : α} {n : ℕ} :
  (f^[n]) (f x) = f ((f^[n]) x) :=
by rw [←function.iterate_succ_apply, function.iterate_succ_apply']

lemma converges_of_le {f : ℕ → ℕ} {n : ℕ} (h : ∀ (n : ℕ), f n ≤ n) : converges f n :=
begin
  change ∃ (_ _ : ℕ), _, induction n using nat.strong_induction_on with n ih, dsimp at ih,
  simp_rw function.iterate_succ_apply', have h₁ := h ((f^[n]) n),
  rw le_iff_lt_or_eq at h₁, cases h₁,
  { replace h₁ : _ < n := gt_of_ge_of_gt (iter_le_of_le h) h₁,
    specialize ih _ h₁, rcases ih with ⟨y, k, h₂, h₃⟩,
    use [y, n + 1 + k], split; simp_rw iter_add,
    { exact h₂ },
    { rwa ←@iter_apply_comm _ f }},
  { exact ⟨_, _, rfl, h₁⟩ },
end

lemma converges_sum_digits {n : ℕ} : converges sum_digits n :=
converges_of_le (λ _, sum_digits_le)

lemma converges_to_fixed {α : Type} [inhabited α] {f : α → α} {z : α}
  (h : converges f z) : converges_to f z (fixed f z) :=
by { cases h with x h, rwa fixed_eq_of_converges_to h }

lemma converges_to_apply {α : Type} {f : α → α} {z x : α}
  (h : converges_to f z x) : converges_to f z (f x) :=
begin
  rcases h with ⟨n, h₁, h₂⟩, use n + 1, split; rw iter_add,
  { rw h₁, refl },
  { rw h₂, refl },
end

lemma apply_converges_to {α : Type} {f : α → α} {z x : α}
  (h : converges_to f z x) : converges_to f (f z) x :=
begin
  rcases h with ⟨k, h₁, h₂⟩, cases k,
  { use 0, split,
    { exact h₂ },
    { cases h₁, rwa [iter_apply_comm, h₂] }},
  { exact ⟨k, h₁, h₂⟩ },
end

lemma apply_converges {α : Type} {f : α → α} {z : α}
  (h : converges f z) : converges f (f z) := ⟨_, apply_converges_to h.some_spec⟩

lemma fixed_eq_fixed_of {α : Type} [inhabited α] {f : α → α} {z₁ z₂ x : α}
  (h₁ : converges_to f z₁ x) (h₂ : converges_to f z₂ x) : fixed f z₁ = fixed f z₂ :=
by rw [fixed_eq_of_converges_to h₁, fixed_eq_of_converges_to h₂]

lemma fixed_apply_eq_of_converges {α : Type} [inhabited α] {f : α → α} {z : α}
  (h : converges f z) : fixed f (f z) = fixed f z :=
by { cases h with x h, exact fixed_eq_fixed_of (apply_converges_to h) h }

lemma digital_root_sum_digits {n : ℕ} : digital_root (sum_digits n) = digital_root n :=
fixed_apply_eq_of_converges converges_sum_digits

lemma fixed_ind {α : Type} [inhabited α] {P : α → Prop} {f : α → α} {z : α}
  (h₁ : converges f z) (h₂ : P z) (h₃ : ∀ (x : α), P x → P (f x)) : P (fixed f z) :=
begin
  cases h₁ with x h₁, rw fixed_eq_of_converges_to h₁,
  rcases h₁ with ⟨n, h₁, -⟩, rw ←h₁, exact function.iterate.rec _ h₃ h₂ _,
end

lemma sum_digits_mod_9 {n : ℕ} : sum_digits n % 9 = n % 9 :=
begin
  induction n using digit_ind with d n h ih,
  { rw sum_digits_zero },
  { rw [sum_digits_digit_add_mul_10 h, nat.add_mod, ih, eq_comm, nat.add_mod,
    nat.mul_mod], congr' 2, change 10 % 9 with 1, rw [nat.mul_one, nat.mod_mod] },
end

lemma digital_root_mod_9 {n : ℕ} : digital_root n % 9 = n % 9 :=
begin
  apply @fixed_ind _ _ (λ (k : ℕ), k % 9 = n % 9) _ _ converges_sum_digits rfl,
  rintro x h, rw [←h, sum_digits_mod_9],
end

lemma digit_mod_10 {d : ℕ} (h : is_digit d) : d % 10 = d :=
nat.mod_eq_of_lt (nat.lt_succ_of_le h)

lemma pos_add_iff {a b : ℕ} : 0 < a + b ↔ 0 < a ∨ 0 < b :=
by { rw ←not_iff_not, push_neg, simp_rw [nat.le_zero_iff, add_eq_zero_iff] }

lemma sum_digits_pos_succ {n : ℕ} : 0 < sum_digits n.succ :=
begin
  induction n using nat.strong_induction_on with n ih, dsimp at ih,
  rw [sum_digits_def, pos_add_iff], by_cases h : n.succ ≤ 9,
  { rw digit_mod_10 h, exact or.inl (nat.succ_pos _) },
  {
    right, push_neg at h, rw nat.lt_succ_iff at h,
    obtain ⟨n, rfl⟩ := nat.exists_eq_add_of_le h, clear h,
    rw [add_comm, ←nat.add_succ, nat.add_div_right _ (nat.succ_pos _)],
    apply ih, rw add_comm, cases n,
    { dec_trivial },
    { apply nat.lt_add_right, apply nat.div_lt_self; dec_trivial }},
end

lemma sum_digits_eq_zero_iff {n : ℕ} : sum_digits n = 0 ↔ n = 0 :=
begin
  split; intro h,
  { cases n,
    { refl },
    { contrapose h, exact ne_of_gt sum_digits_pos_succ }},
  { subst h, exact sum_digits_zero },
end

lemma digital_root_eq_zero_iff {n : ℕ} : digital_root n = 0 ↔ n = 0 :=
begin
  apply @fixed_ind _ _ (λ (k : ℕ), k = 0 ↔ n = 0) _ _ converges_sum_digits (iff.refl _),
  rintro x h, rw [←h, sum_digits_eq_zero_iff],
end

lemma digit_mod_9_eq_zero_iff {d : ℕ} (h : is_digit d) : d % 9 = 0 ↔ d = 0 ∨ d = 9 :=
begin
  rw is_digit at h, split; intro h₁,
  { cases d,
    { exact or.inl rfl },
    { rw le_iff_eq_or_lt at h, cases h,
      { exact or.inr h },
      { rw nat.mod_eq_of_lt h at h₁, cases h₁ }}},
  { cases h₁; subst d; refl },
end

lemma digital_root_eq_of_pos {n : ℕ} (h : 0 < n) : digital_root n = modp n 9 :=
begin
  cases n,
  { cases h },
  { rw modp, split_ifs with h₁;
    rw [←digital_root_mod_9, digit_mod_9_eq_zero_iff is_digit_digital_root] at h₁,
    { cases h₁,
      { rw digital_root_eq_zero_iff at h₁, cases h₁ },
      { exact h₁ }},
    { rw not_or_distrib at h₁, cases h₁ with h₁ h₂,
      rw [←digital_root_mod_9, nat.mod_eq_of_lt],
      exact lt_of_le_of_ne is_digit_digital_root h₂ }},
end

lemma digital_root_succ {n : ℕ} : digital_root n.succ = modp n.succ 9 :=
digital_root_eq_of_pos (nat.succ_pos _)

lemma eq_zero_of_modp_eq_zero {k n : ℕ} (h : modp n k = 0) : n = 0 :=
begin
  rw modp at h, split_ifs at h with h₁,
  { subst k, rwa nat.mod_zero at h₁ },
  { contradiction },
end

lemma succ_mod_eq_zero_iff {k n : ℕ} (h : 0 < k) : n.succ % k = 0 ↔ n % k = k - 1 :=
begin
  sorry
end

-- #exit

lemma succ_mod_eq_succ_iff {k n r : ℕ} (h : 0 < k) : n.succ % k = r.succ ↔ n % k = r :=
begin
  sorry
end

lemma digital_root_mod_9_eq_of_ne_9 {n : ℕ} (h : digital_root n ≠ 9) :
  digital_root n % 9 = digital_root n :=
nat.mod_eq_of_lt (lt_of_le_of_ne is_digit_digital_root h)

lemma digital_root_succ_eq_of_ne_9 {n : ℕ} (h : digital_root n ≠ 9) :
  digital_root n.succ = (digital_root n).succ :=
begin
  rw [digital_root_eq_of_pos (nat.succ_pos _), modp], split_ifs with h₁,
  { rw [succ_mod_eq_zero_iff (nat.succ_pos _), ←digital_root_mod_9,
    digital_root_mod_9_eq_of_ne_9 h] at h₁, rw h₁ },
  { cases n,
    { rw digital_root_zero, refl },
    { rw [digital_root_eq_of_pos (nat.succ_pos _), modp], split_ifs with h₂,
      { rw [←digital_root_mod_9, digital_root_mod_9_eq_of_ne_9 h,
        digital_root_eq_zero_iff] at h₂, cases h₂ },
      { rw succ_mod_eq_succ_iff (nat.succ_pos _) }}},
end

lemma digital_root_succ_eq_sum_digits {n : ℕ} :
  digital_root n.succ = sum_digits (digital_root n).succ :=
begin
  rw [eq_comm, digital_root_succ, modp,
  sum_digits_digit_add_digit is_digit_digital_root (dec_trivial : is_digit 1)],
  simp_rw ←nat.add_one, split_ifs with h₁ h₂ h₂,
  { rw [←digital_root_mod_9, digit_mod_9_eq_zero_iff is_digit_digital_root] at h₂,
    cases h₂,
    { rw digital_root_eq_of_pos (nat.succ_pos _) at h₂, cases eq_zero_of_modp_eq_zero h₂ },
    { rw nat.succ_le_iff at h₁, rw [nat.succ_inj', ←nat.mod_eq_of_lt h₁, digital_root_mod_9],
      apply_fun (λ n, n % 9) at h₂, rwa [nat.mod_self, digital_root_mod_9,
      succ_mod_eq_zero_iff (nat.succ_pos _)] at h₂ }},
  { rw [←digital_root_mod_9, digit_mod_9_eq_zero_iff is_digit_digital_root,
    not_or_distrib] at h₂, cases h₂ with h₂ h₃,
    have h₄ := lt_of_le_of_ne is_digit_digital_root h₃,
    rw [←digital_root_mod_9, nat.mod_eq_of_lt h₄, digital_root_succ_eq_of_ne_9],
    exact ne_of_lt (nat.lt_of_succ_le h₁) },
  { replace h₁ : digital_root n = 9,
    { contrapose! h₁,
      exact nat.succ_le_of_lt (lt_of_le_of_ne is_digit_digital_root h₁) },
    rw [succ_mod_eq_zero_iff (nat.succ_pos _), ←digital_root_mod_9, h₁] at h₂, cases h₂ },
  { replace h₁ : digital_root n = 9,
    { contrapose! h₁,
      exact nat.succ_le_of_lt (lt_of_le_of_ne is_digit_digital_root h₁) },
    symmetry, rw [h₁, succ_mod_eq_succ_iff (nat.succ_pos _), ←digital_root_mod_9, h₁], refl },
end

-- #exit

lemma digital_root_add {m n : ℕ} :
  digital_root (m + n) = sum_digits (digital_root m + digital_root n) :=
begin
  sorry
end

#exit

lemma digital_root_add_eq_sum_digits {m n : ℕ} :
  digital_root (m + n) = sum_digits (digital_root m + digital_root n) :=
begin
  induction n with n ih generalizing m,
  sorry {
    simp_rw [digital_root_zero, add_zero, sum_digits_digital_root],
  },
  {
    rw [nat.add_succ, ←nat.succ_add, ih, ←nat.one_add n, ih],
  },
end

#exit

lemma digital_root_digit_add_mul_10 {d n : ℕ} (h : is_digit d) :
  digital_root (d + n * 10) = sum_digits (d + digital_root n) :=
begin
  rw sum_digits_digit_add_digit h is_digit_digital_root,
end

#exit

lemma digital_root_eq_modp_of_pos {n : ℕ} (h : 0 < n) : digital_root n = modp n 9 :=
begin
  induction n using digit_ind with n d h₁ ih,
  { cases h },
  { cases n,
    { simp_rw [zero_mul, add_zero] at h ⊢,
      rw [modp_digit_of_pos h₁ h, digital_root_digit_eq_self h₁ h] },
    { specialize ih (nat.succ_pos _),
      rw [digital_root_digit_add_mul_10 h₁, modp_digit_add_mul_10 h₁, ih,
      sum_digits_digit_add_digit h₁ is_digit_modp_9],
      split_ifs with h,
      { cases d,
        { simp },
        { rw [modp_add, modp_digit_of_pos h₁ (nat.succ_pos _),
          modp_digit_add_digit h₁ is_digit_modp_9 (nat.succ_pos _)
          (modp_pos_of_pos (nat.succ_pos _)), if_pos h] }},
      { have h₂ : 0 < d,
        { contrapose! h, rw nat.le_zero_iff at h, subst d,
          rw zero_add, apply modp_le, dec_trivial },
        rw [modp_add, modp_digit_of_pos h₁ h₂], revert h,
        generalize h₃ : modp n.succ 9 = d₂, intro h, have h₄ : 0 < d₂,
        { subst d₂, exact modp_pos_of_pos (nat.succ_pos _) },
        have h₅ : is_digit d₂,
        { subst d₂, exact is_digit_modp_9 },
        rw [modp_digit_add_digit h₁ h₅ h₂ h₄, if_neg h] }}},
end

lemma digital_root_def {n : ℕ} :
  digital_root n = if n = 0 then 0 else if n % 9 = 0 then 9 else n % 9 :=
begin
  rw ←modp, split_ifs with h h₁,
  { cases h, exact digital_root_zero },
  { exact digital_root_eq_modp_of_pos (pos_iff_ne_zero.mpr h) },
end