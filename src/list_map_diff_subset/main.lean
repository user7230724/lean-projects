import tactic
import tactic.induction
import data.list.basic
import data.multiset.basic

noncomputable theory
open_locale classical
open_locale big_operators

lemma nat.pred_eq_self_iff {n : ℕ} : n.pred = n ↔ n = 0 :=
begin
  cases n; simp,
  exact (nat.succ_ne_self _).symm,
end

lemma list.count_erase {α : Type*} {l : list α} {x : α} :
  (l.erase x).count x = l.count x - (ite (x ∈ l) 1 0) :=
begin
  split_ifs with h,
  { rw list.count_erase_self, refl },
  { have h₁ : x ∉ l.erase x,
    { contrapose! h, exact list.mem_of_mem_erase h },
    rw [list.count_eq_zero_of_not_mem h, list.count_eq_zero_of_not_mem h₁] },
end

lemma list.mem_diff_iff {α : Type*} {l₁ l₂ : list α} {x : α} :
  x ∈ l₁ \ l₂ ↔ l₂.count x < l₁.count x :=
begin
  change x ∈ list.diff _ _ ↔ _,
  induction l₂ with hd l₂ ih generalizing l₁; simp,
  rw [ih, list.count_cons], split_ifs,
  { subst h, split; intro h,
    { rw list.count_erase at h, split_ifs at h with h₁,
      { cases list.count x l₁,
        { cases h },
        { rwa nat.succ_lt_succ_iff } },
      { rw ←list.count_pos at h₁, push_neg at h₁,
        rw nat.le_zero_iff at h₁, rw h₁ at h, cases h }},
    { rw list.count_erase, split_ifs with h₁,
      { rwa lt_tsub_iff_right },
      { rw ←list.count_pos at h₁, push_neg at h₁,
        rw nat.le_zero_iff at h₁, rw h₁ at h, cases h }}},
  { rw list.count_erase_of_ne h },
end

lemma finset.sum_le_sum_of_le {α : Type*} {f g : α → ℕ} {s : finset α}
  (h : ∀ (a : α), a ∈ s → f a ≤ g a) :
  ∑ (a : α) in s, f a ≤ ∑ (a : α) in s, g a :=
begin
  revert h, apply s.induction_on; simp,
  rintro a s h₁ h₂ h₃ h₄, specialize h₂ h₄,
  simp_rw finset.sum_insert h₁, exact add_le_add h₃ h₂,
end

lemma list.sum_count_cons_diff_singleton {α : Type*} {l : list α} {x : α} :
  ∑ (a : α) in l.to_finset \ {x}, (x :: l).count a =
  ∑ (a : α) in l.to_finset \ {x}, l.count a :=
begin
  apply finset.sum_congr rfl, rintro a h, rw [list.count_cons, if_neg],
  rintro rfl, rw [finset.mem_sdiff, finset.mem_singleton] at h, exact h.2 rfl,
end

lemma list.sum_count_cons {α : Type*} {l : list α} {x : α} :
  ∑ (a : α) in l.to_finset, (x :: l).count a =
  ∑ (a : α) in l.to_finset, l.count a + ite (x ∈ l) 1 0 :=
begin
  simp_rw ←list.mem_to_finset, split_ifs,
  { simp_rw finset.sum_eq_sum_diff_singleton_add h,
    rw [list.sum_count_cons_diff_singleton, add_assoc],
    congr, rw [list.count_cons, if_pos rfl] },
  { have h₁ : l.to_finset = l.to_finset \ {x},
    { exact (finset.sdiff_singleton_not_mem_eq_self _ h).symm },
    rw h₁, exact list.sum_count_cons_diff_singleton },
end

lemma list.length_eq_sum_count {α : Type*} {l : list α} :
  l.length = ∑ (x : α) in l.to_finset, l.count x :=
begin
  induction l with hd l ih; simp, by_cases h : hd ∈ l.to_finset,
  { rw finset.insert_eq_of_mem h,
    rw finset.sum_eq_sum_diff_singleton_add h at ih ⊢,
    rw [list.sum_count_cons_diff_singleton, list.count_cons, if_pos rfl, ih],
    refl },
  { have h₁ : hd ∈ insert hd l.to_finset := finset.mem_insert_self _ _,
    rw finset.sum_eq_sum_diff_singleton_add h₁, have h₂ : hd ∉ l,
    { rwa list.mem_to_finset at h },
    have h₃ : insert hd l.to_finset \ {hd} = l.to_finset,
    { ext x, by_cases h₃ : x = hd,
      { subst h₃, simpa [h₁] },
      { simp [h₃] }},
    rw h₃, have h₃ : list.count hd (hd :: l) = 1,
    { rw [list.count_cons, if_pos rfl, list.count_eq_zero_of_not_mem h₂] },
    rw h₃, congr, rw [ih, list.sum_count_cons, if_neg h₂], refl },
end

lemma list.sum_union_eq_sum {α : Type*} {l : list α} {s : finset α} :
  ∑ (x : α) in l.to_finset ∪ s, l.count x = ∑ (x : α) in l.to_finset, l.count x :=
begin
  apply s.induction_on; simp, rintro a s h₁ ih,
  by_cases h₃ : a ∈ l.to_finset ∪ s,
  { rwa finset.insert_eq_of_mem h₃ },
  { rw [finset.sum_insert h₃, ih], have h₄ : a ∉ l,
    { contrapose! h₃, apply finset.mem_union_left, rwa list.mem_to_finset },
    rw [list.count_eq_zero_of_not_mem h₄, zero_add] },
end

lemma list.length_le_length_of_count_le_count {α : Type*}
  {l₁ l₂ : list α} (h : ∀ (a : α), l₁.count a ≤ l₂.count a) :
  l₁.length ≤ l₂.length :=
begin
  simp_rw list.length_eq_sum_count,
  let s := l₁.to_finset ∪ l₂.to_finset,
  suffices h₁ : ∑ (x : α) in s, l₁.count x ≤ ∑ (x : α) in s, l₂.count x,
  { change s with _ ∪ _ at h₁, nth_rewrite 1 finset.union_comm at h₁,
    simp_rw list.sum_union_eq_sum at h₁, exact h₁ },
  replace h : ∀ (a : α), a ∈ s → l₁.count a ≤ l₂.count a,
  { rintro a h₁, apply h },
  exact finset.sum_le_sum_of_le h,
end

lemma list.count_map_eq_length_filter {α β : Type*} {f : α → β}
  {l : list α} {y : β} :
  (l.map f).count y = (l.filter (λ (x : α), f x = y)).length :=
begin
  induction l with hd l ih; simp,
  rw list.count_cons, rw ih, clear ih,
  split_ifs; rw list.filter,
  { rw if_pos h.symm, refl },
  { rw if_neg, tauto },
end

lemma list.count_filter_eq_ite {α : Type*} {P : α → Prop}
  {l : list α} {x : α} : (l.filter P).count x = ite (P x) (l.count x) 0 :=
begin
  split_ifs,
  { exact list.count_filter h },
  { apply list.count_eq_zero_of_not_mem,
    contrapose! h, exact list.of_mem_filter h },
end

example {α β : Type*} {f : α → β} {l₁ l₂ : list α} :
  l₁.map f \ l₂.map f ⊆ (l₁ \ l₂).map f :=
begin
  rintro y h, rw list.mem_diff_iff at h, rw list.mem_map,
  contrapose! h, simp_rw [list.mem_diff_iff, imp_not_comm, not_lt] at h,
  let s₁ := l₁.filter (λ x, f x = y), let s₂ := l₂.filter (λ x, f x = y),
  have hs₁ : ∀ (a : α), s₁.count a = ite (f a = y) (l₁.count a) 0,
  { exact λ _, list.count_filter_eq_ite },
  have hs₂ : ∀ (a : α), s₂.count a = ite (f a = y) (l₂.count a) 0,
  { exact λ _, list.count_filter_eq_ite },
  replace h : ∀ (a : α), s₁.count a ≤ s₂.count a,
  { rintro a, specialize h a, rw [hs₁, hs₂],
    split_ifs with h₁,
    { exact h h₁ },
    { refl }},
  have hh₁ : (l₁.map f).count y = s₁.length := list.count_map_eq_length_filter,
  have hh₂ : (l₂.map f).count y = s₂.length := list.count_map_eq_length_filter,
  rw [hh₁, hh₂], exact list.length_le_length_of_count_le_count h,
end