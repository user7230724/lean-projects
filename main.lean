import tactic.induction
import data.int.basic
import data.set.basic
import logic.function.iterate

import .point .dist .board .state .move .game

noncomputable theory
open_locale classical

-- Keep definitions intuitive!
-- Do not generalize too much!

def play {pw : ℕ} (a : Angel pw) (d : Devil) (n : ℕ) :=
play_at (init_game a d) n

def angel_wins {pw : ℕ} (a : Angel pw) (d : Devil) :=
angel_wins_at (init_game a d)

def devil_wins {pw : ℕ} (a : Angel pw) (d : Devil) :=
devil_wins_at (init_game a d)

def angel_hws (pw : ℕ) :=
∃ (a : Angel pw), ∀ (d : Devil), angel_wins a d

def devil_hws (pw : ℕ) :=
∃ (d : Devil), ∀ (a : Angel pw), devil_wins a d

-----

lemma angel_pw_0_not_hws : ¬angel_hws 0 :=
begin
  rintro ⟨st, h⟩, fapply h default, use 1, clear h,
  change Game.done (ite _ _ _), split_ifs, { exact h }, clear h,
  change Game.done (dite _ _ _), split_ifs, swap, { trivial },
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

lemma angel_wins_at_play_of {pw : ℕ} {g : Game pw}
  (h : angel_wins_at g) {n : ℕ} : angel_wins_at (play_at g n) :=
begin
  intro k, specialize h (k + n),
  rw [play_at, function.iterate_add] at h, exact h,
end

lemma angel_wins_at_play_move_of {pw : ℕ} {g : Game pw}
  (h : angel_wins_at g) : angel_wins_at (play_move_at g) :=
@angel_wins_at_play_of _ _ h 1

lemma play_angel_move_at_players_eq {pw : ℕ} {g : Game pw} :
  (play_angel_move_at g).a = g.a ∧ (play_angel_move_at g).d = g.d :=
by { rw [play_angel_move_at], split_ifs; exact ⟨rfl, rfl⟩ }

lemma play_devil_move_at_players_eq {pw : ℕ} {g : Game pw} :
  (play_devil_move_at g).a = g.a ∧ (play_devil_move_at g).d = g.d :=
by { rw [play_devil_move_at], exact ⟨rfl, rfl⟩ }

lemma play_move_at_players_eq {pw : ℕ} {g : Game pw} :
  (play_move_at g).a = g.a ∧ (play_move_at g).d = g.d :=
begin
  rw [play_move_at],
  split_ifs, exact ⟨rfl, rfl⟩,
  rw [play_angel_move_at_players_eq.1, play_angel_move_at_players_eq.2],
  rw [play_devil_move_at_players_eq.1, play_devil_move_at_players_eq.2],
  exact ⟨rfl, rfl⟩,
end

lemma play_move_at_angel_eq {pw : ℕ} {g : Game pw} :
  (play_move_at g).a = g.a :=
play_move_at_players_eq.1

lemma play_move_at_devil_eq {pw : ℕ} {g : Game pw} :
  (play_move_at g).d = g.d :=
play_move_at_players_eq.2

-----

def mk_angel_pw_ge {pw pw₁ : ℕ} (a : Angel pw)
  (h₁ : pw ≤ pw₁) : Angel pw₁ :=
begin
  refine ⟨λ s h, _⟩,
  refine dite (angel_has_valid_move pw s.board) (λ h₂, _) (λ h₂, _),
  { have v := a.f s h₂, refine ⟨v.1, v.2.1, v.2.2.1.trans h₁, v.2.2.2⟩ },
  { refine ⟨_, h.some_spec⟩ },
end

lemma angel_pw_ge_hws_of {pw pw₁ : ℕ}
  (h₁ : pw ≤ pw₁) (h₂ : angel_hws pw) : angel_hws pw₁ :=
begin
  sorry
end

#exit

-----

theorem angel_hws_iff_pw_ge_2 {pw : ℕ} :
  angel_hws pw ↔ 2 ≤ pw :=
begin
  cases pw, simp [angel_pw_0_not_hws],
  cases pw, simp [angel_pw_1_not_hws], simp [nat.succ_le_succ],
  refine angel_pw_ge_hws_of _ angel_pw_2_hws, simp [nat.succ_le_succ],
end

-- example {a : ℤ}
--   (h : 0 < a) :
--   int.to_nat 0 < a.to_nat :=
-- begin
--   library_search,
-- end