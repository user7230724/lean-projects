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

lemma angel_pw_0_has_not_win_st : ¬angel_hws 0 :=
begin
  sorry
  -- rintro ⟨st, h⟩, apply h default, clear h, use 1,
  -- change Game.done (ite _ _ _), split_ifs, { exact h }, clear h,
  -- change Game.done (dite _ _ _), split_ifs, swap, { trivial },
  -- rcases h with ⟨p, h₁, h₂, h₃⟩,
  -- rw [nat.le_zero_iff, dist_eq_zero_iff] at h₂, contradiction,
end

lemma angel_pw_1_has_not_win_st : ¬angel_hws 1 :=
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

lemma play_done_iff_of_play_state_eq {pw₁ pw₂ n : ℕ}
  {a₁ : Angel pw₁} {a₂ : Angel pw₂} {d₁ d₂ : Devil}
  (h : (play a₁ d₁ n).s = (play a₂ d₂ n).s) :
  (play a₁ d₁ n).done ↔ (play a₂ d₂ n).done :=
begin
  sorry
end

lemma play_move_at_state_eq_of_angel_eq {pw pw₁ : ℕ}
  {g : Game pw} {a₁ : Angel pw₁}
  (h₁ : ∀ {s} h, ∃ h₁, (a₁ s h₁).m = (g.a s h).m)
  (h₂ : angel_wins_at g) :
  (play_move_at (g.set_angel a₁)).s = (play_move_at g).s :=
begin
  sorry
end

lemma play_at_state_eq_of_angel_eq {pw pw₁ n : ℕ}
  {g : Game pw} {a₁ : Angel pw₁}
  (h₁ : ∀ {s} h, ∃ h₁, (a₁ s h₁).m = (g.a s h).m)
  (h₂ : angel_wins_at g) :
  (play_at (g.set_angel a₁) n).s = (play_at g n).s :=
begin
  induction n with n ih, refl,
  simp_rw play_at_succ',
  have h₃ : play_at (g.set_angel a₁) n = (play_at g n).set_angel a₁,
  {
    clear ih,
    sorry
  },
  rw h₃, clear h₃,
  apply play_move_at_state_eq_of_angel_eq,
  {
    rintro s h,
    have h₃ : angel_has_valid_move pw₁ s.board,
    sorry,
    use h₃,
    rw play_at_angel_eq,
    exact (@h₁ s h).some_spec,
  },
  {
    rw angel_wins_at_play_at_iff,
    exact h₂,
  },
end

#exit

lemma play_state_eq_of_angel_eq {pw pw₁ n : ℕ}
  {a : Angel pw} {a₁ : Angel pw₁} {d : Devil}
  (h₁ : ∀ {s} h, ∃ h₁, (a₁ s h₁).m = (a s h).m)
  (h₂ : angel_wins a d) :
  (play a₁ d n).s = (play a d n).s :=
begin
  apply @play_at_state_eq_of_angel_eq _ _ _ (init_game a d),
  { exact λ s h, h₁ h },
  { exact h₂ },
end

def mk_angel_pw_ge {pw pw₁ : ℕ} (a : Angel pw)
  (h₁ : pw ≤ pw₁) : Angel pw₁ :=
begin
  rintro s h,
  refine dite (angel_has_valid_move pw s.board) (λ h₂, _) (λ h₂, _),
  { have v := a s h₂, refine ⟨v.1, v.2.1, v.2.2.1.trans h₁, v.2.2.2⟩ },
  { refine ⟨_, h.some_spec⟩ },
end

lemma angel_pw_ge_hws_of {pw pw₁ : ℕ}
  (h₁ : pw ≤ pw₁) (h₂ : angel_hws pw) : angel_hws pw₁ :=
begin
  cases h₂ with a h₂, use mk_angel_pw_ge a h₁,
  rintro d n, specialize h₂ d,
  refine mt (play_done_iff_of_play_state_eq _).mp (h₂ n),
  refine play_state_eq_of_angel_eq _ h₂, clear' d n h₂,
  rintro s h, have h₂ := angel_has_valid_move_ge_of h₁ h, use h₂,
  unfold mk_angel_pw_ge, simp, split_ifs, refl,
end

#exit

-----

theorem angel_hws_iff_pw_ge_2 {pw : ℕ} :
  angel_hws pw ↔ 2 ≤ pw :=
begin
  cases pw, simp [angel_pw_0_has_not_win_st],
  cases pw, simp [angel_pw_1_has_not_win_st], simp [nat.succ_le_succ],
  refine angel_pw_ge_hws_of _ angel_pw_2_hws, simp [nat.succ_le_succ],
end

-- example {a : ℤ}
--   (h : 0 < a) :
--   int.to_nat 0 < a.to_nat :=
-- begin
--   library_search,
-- end