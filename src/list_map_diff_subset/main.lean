import tactic
import tactic.induction
import data.list.basic
import data.multiset.basic

noncomputable theory
open_locale classical
open_locale big_operators

-- lemma list.count_cons_cons {α : Type*} {l : list α} {hd₁ hd₂ x : α} :
--   (hd₁ :: hd₂ :: l).count x = (hd₂ :: hd₁ :: l).count x :=
-- begin
--   simp_rw list.count_cons,
--   split_ifs; refl,
-- end

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

-- #exit

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

-- lemma list.count_map_le_count_map {α : Type}
--   {P : α → Prop} {l₁ l₂ : list α}
--   (h : ∀ (a : α), P a → l₁.count a ≤ l₂.count a) :
--   l₁.count 

-- #exit

lemma list.length_eq_sum_count {α : Type*}
  {l : list α} : l.length = ∑ (x : α) in l.to_finset, l.count x :=
begin
  sorry
  -- induction l with hd l ih; simp,
  -- rw ih, clear ih,
  -- let s := l.to_finset,
  -- let s' := insert hd s,
  -- change l.to_finset with s,
  -- change insert hd s with s',
  -- have h : hd ∈ s',
  -- sorry,
  -- rw finset.sum_eq_sum_diff_singleton_add h,
  -- have h₁ : ∑ (x : α) in s' \ {hd}, list.count x (hd :: l) =
  --   ∑ (x : α) in s' \ {hd}, list.count x l,
  -- sorry,
  -- rw h₁, clear h₁,
end

-- #exit

lemma list.length_le_length_of_count_le_count {α : Type*}
  {l₁ l₂ : list α} (h : ∀ (a : α), l₁.count a ≤ l₂.count a) :
  l₁.length ≤ l₂.length :=
begin
  sorry
  -- induction l₁ with x l₁ ih generalizing l₂; simp,
  -- cases l₂ with y l₂,
  -- {
  --   specialize h x,
  --   rw list.count_cons at h,
  --   rw if_pos rfl at h,
  --   cases h,
  -- },
  -- {
  --   simp,
  --   apply ih, clear ih,
  --   intro a,
  --   have h₁ := h a,
  --   simp_rw list.count_cons at h₁,
  --   split_ifs at h₁ with h₂ h₃ h₄,
  --   {
  --     rwa nat.succ_le_succ_iff at h₁,
  --   },
  --   {
  --     exact nat.le_of_succ_le h₁,
  --   },
  --   {
  --     subst a,
  --     replace h₂ : x ≠ y := by tauto,
  --     replace h := id h,
  --     replace h₁ := id h₁,
  --   },
  --   {
  --     exact h₁,
  --   },
  -- },
end

#exit

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

example {α β : Type*} {f : α → β} {l₁ l₂ : list α} :
  l₁.map f \ l₂.map f ⊆ (l₁ \ l₂).map f :=
begin
  rintro y h,
  rw list.mem_diff_iff at h,
  rw list.mem_map,
  contrapose! h,
  simp_rw [list.mem_diff_iff, imp_not_comm, not_lt] at h,

  let s₁ := l₁.filter (λ x, f x = y),
  let s₂ := l₂.filter (λ x, f x = y),

  have hs₁ : ∀ (a : α), s₁.count a = ite (f a = y) (l₁.count a) 0,
  sorry;{
    rintro a,
    change s₁ with list.filter _ _,
    split_ifs with h₁,
    {
      rw list.count_filter,
      exact h₁,
    },
    {
      apply list.count_eq_zero_of_not_mem,
      rw list.mem_filter,
      simp [h₁],
    },
  },
  have hs₂ : ∀ (a : α), s₂.count a = ite (f a = y) (l₂.count a) 0,
  sorry,

  replace h : ∀ (a : α), s₁.count a ≤ s₂.count a,
  sorry;{
    rintro a,
    specialize h a,
    rw [hs₁, hs₂],
    split_ifs with h₁,
    {
      exact h h₁,
    },
    {
      refl
    },
  },

  have hh₁ : (l₁.map f).count y = s₁.length := list.count_map_eq_length_filter,
  have hh₂ : (l₂.map f).count y = s₂.length := list.count_map_eq_length_filter,
  rw [hh₁, hh₂],
  exact list.length_le_length_of_count_le_count h,
end