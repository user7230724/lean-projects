import tactic.induction
import data.int.basic
import data.set.basic

import .point .dist .board .state .move .game

noncomputable theory
open_locale classical

-- Keep definitions intuitive!
-- Do not generalize too much!

def angel_wins {pw : ℕ} (a : Angel_st pw) (d : Devil_st) :=
angel_wins_at (init_game a d)

def devil_wins {pw : ℕ} (a : Angel_st pw) (d : Devil_st) :=
¬angel_wins a d

def angel_hws (pw : ℕ) :=
∃ (a : Angel_st pw), ∀ (d : Devil_st), angel_wins a d

def devil_hws (pw : ℕ) :=
∃ (d : Devil_st), ∀ (a : Angel_st pw), devil_wins a d

-----

lemma angel_pw_0_has_not_win_st : ¬angel_hws 0 :=
begin
  rintro ⟨st, h⟩, apply h default, clear h, use 1,
  change Game.done (ite _ _ _), split_ifs, { exact h }, clear h,
  change Game.done (dite _ _ _), split_ifs, swap, { trivial },
  rcases h with ⟨p, h₁, h₂, h₃⟩,
  rw [nat.le_zero_iff, dist_eq_zero_iff] at h₂, contradiction,
end

lemma angel_pw_1_has_not_win_st : ¬angel_hws 1 :=
begin
  sorry
end

lemma angel_pw_2_hws : angel_hws 2 :=
begin
  sorry
end

lemma angel_pw_ge_hws_of_angel_hws {pw₁ pw₂ : ℕ}
  (h₁ : angel_hws pw₁) (h₂ : pw₁ ≤ pw₂) : angel_hws pw₂ :=
begin
  sorry
end

-----

theorem angel_hws_iff_pw_ge_2 {pw : ℕ} :
  angel_hws pw ↔ 2 ≤ pw :=
begin
  cases pw, simp [angel_pw_0_has_not_win_st],
  cases pw, simp [angel_pw_1_has_not_win_st], simp [nat.succ_le_succ],
  apply angel_pw_ge_hws_of_angel_hws angel_pw_2_hws, simp [nat.succ_le_succ],
end

#exit

example {a : ℤ}
  (h : 0 < a) :
  int.to_nat 0 < a.to_nat :=
begin
  library_search,
end