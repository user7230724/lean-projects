import tactic.induction
import data.int.basic
import data.set.basic
import logic.function.iterate

import .point .dist .board .state .move .game
import .angel_pw_ge

noncomputable theory
open_locale classical

-- Keep definitions intuitive!
-- Do not generalize too much!

def play {pw : ℕ} (a : Angel pw) (d : Devil) (n : ℕ) :=
(init_game a d).play n

def angel_wins {pw : ℕ} (a : Angel pw) (d : Devil) :=
(init_game a d).angel_wins

def devil_wins {pw : ℕ} (a : Angel pw) (d : Devil) :=
(init_game a d).devil_wins

def angel_hws (pw : ℕ) := angel_hws_at pw state₀
def devil_hws (pw : ℕ) := devil_hws_at pw state₀

-----

lemma angel_pw_0_not_hws : ¬angel_hws 0 :=
begin
  rintro ⟨a, h⟩, contrapose! h, clear h, use default,
  rw not_angel_wins_at, use 1,
  change ¬Game.act (ite _ _ _), split_ifs,
  swap, { exact (h trivial).elim }, clear h,
  change ¬Game.act (dite _ _ _), split_ifs, swap, { trivial },
  rcases h with ⟨p, h₁, h₂, h₃⟩,
  rw [nat.le_zero_iff, dist_eq_zero_iff] at h₂, contradiction,
end

lemma angel_pw_1_not_hws : ¬angel_hws 1 :=
begin
  sorry
end

lemma angel_pw_2_hws : angel_hws 2 :=
begin
  sorry
end

-----

lemma angel_pw_ge_hws {pw pw₁ : ℕ}
  (h₁ : pw ≤ pw₁) (h₂ : angel_hws pw) : angel_hws pw₁ :=
begin
  cases h₂ with a h₂, use mk_angel_pw_ge a h₁,
  intro d, specialize h₂ d, apply mk_angel_pw_ge_wins_at_of h₂,
end

-----

theorem angel_hws_iff_pw_ge_2 {pw : ℕ} :
  angel_hws pw ↔ 2 ≤ pw :=
begin
  cases pw, simp [angel_pw_0_not_hws],
  cases pw, simp [angel_pw_1_not_hws], simp [nat.succ_le_succ],
  refine angel_pw_ge_hws _ angel_pw_2_hws, simp [nat.succ_le_succ],
end

-- example {a : ℤ}
--   (h : 0 < a) :
--   int.to_nat 0 < a.to_nat :=
-- begin
--   library_search,
-- end