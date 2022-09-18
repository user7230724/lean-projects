import tactic
import tactic.induction

noncomputable theory
open_locale classical

def mk_stat (P : Prop) (n k : ℕ) : ℕ → Prop
| 0 := (n = k → P) → P
| (i+1) := (n = k - i - 1 → P) → mk_stat i

def mk_list (P : Prop) (n k : ℕ) : ℕ → list Prop
| 0 := [n = k → P]
| (i+1) := (n = k - i - 1 → P) :: mk_list i

def mk_stat' (P : Prop) (n k i : ℕ) : Prop :=
(∀ (Q ∈ mk_list P n k i), Q) → P

@[simp]
lemma aux₁ {P Q : Prop} : (P → Q) → Q ↔ P ∨ Q :=
by tauto

lemma mk_stat_of {P : Prop} {n k i : ℕ} (h : mk_stat' P n k i) : mk_stat P n k i :=
begin
  rw mk_stat' at h, induction i with i hi; intro h₁,
  { apply h, rintro Q h₂, rw [mk_list, list.mem_singleton] at h₂, subst h₂, exact h₁ },
  { apply hi, intro h₂, apply h, intro Q, simp_rw [mk_list, list.mem_cons_iff], rintro (rfl | h₃),
    { exact h₁ },
    { exact h₂ _ h₃ }},
end

lemma mem_mk_list {P Q : Prop} {n k i : ℕ} :
  Q ∈ mk_list P n k i ↔ Q = (n = k → P) ∨ ∃ (j : ℕ), j < i ∧ Q = (n = k - j - 1 → P) :=
begin
  split; intro h,
  { induction i with i ih,
    { rw [mk_list, list.mem_singleton] at h, simp [h] },
    { rw or_iff_not_imp_left, intro h₁, rw [mk_list, list.mem_cons_iff] at h, rcases h with (rfl | h),
      { exact ⟨i, nat.lt_succ_self _, rfl⟩ },
      { rw or_iff_not_imp_left at ih, specialize ih h h₁,
        rcases ih with ⟨j, h₁, h₂⟩, refine ⟨j, nat.lt_succ_of_lt h₁, h₂⟩ }}},
  { rcases h with (rfl | h),
    { induction i with i hi,
      { simp [mk_list, list.mem_cons_iff] },
      { rw [mk_list, list.mem_cons_iff], exact or.inr hi }},
    { rcases h with ⟨j, h, rfl⟩, induction i with i hi,
      { cases h },
      { rw [nat.lt_succ_iff, le_iff_eq_or_lt] at h, rcases h with (rfl | h),
        { simp [mk_list, list.mem_cons_iff] },
        { rw [mk_list, list.mem_cons_iff], exact or.inr (hi h) }}}},
end

lemma le_cases {n k : ℕ} {P : Prop} (h : n ≤ k) : mk_stat P n k k :=
begin
  apply mk_stat_of, intro h₁, simp_rw mem_mk_list at h₁,
  rw le_iff_eq_or_lt at h, rcases h with (rfl | h),
  { exact h₁ _ (or.inl rfl) rfl },
  { obtain ⟨k, rfl⟩ := nat.exists_eq_add_of_lt h,
    apply h₁ _ (or.inr ⟨k, by linarith, rfl⟩),
    calc n = n + (k + 1) - (k + 1) : eq_tsub_of_add_eq rfl },
end

example {n : ℕ} (h : n ≤ 2) : true :=
begin
  apply le_cases h; intro h,
  all_goals {triv},
end