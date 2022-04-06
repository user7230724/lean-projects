import tactic
import tactic.induction

import .base .game .pw_ge

noncomputable theory
open_locale classical

def play {pw : ℕ} (a : A pw) (d : D) (n : ℕ) :=
(init_game a d state₀).play n

def A_wins {pw : ℕ} (a : A pw) (d : D) :=
(init_game a d state₀).A_wins

def D_wins {pw : ℕ} (a : A pw) (d : D) :=
(init_game a d state₀).D_wins

def D_hws (pw : ℕ) := D_hws_at pw state₀

-----

lemma A_pw_0_not_hws : ¬A_hws 0 :=
begin
  rintro ⟨a, h⟩, contrapose! h, clear h, use default, rw not_A_wins_at, use 1,
  rw [play_1, play_move_at_act], swap, { triv },
  rw [play_A_move_at, dif_neg], { exact not_false },
  push_neg, rintro h₁ ⟨ma, h₂, h₃, h₄⟩,
  rw [nat.le_zero_iff, dist_eq_zero_iff] at h₃, contradiction,
end

lemma A_pw_1_not_hws : ¬A_hws 1 :=
begin
  sorry
end

lemma A_pw_2_hws : A_hws 2 :=
begin
  sorry
end

-----

lemma A_pw_ge_hws {pw pw₁ : ℕ}
  (h₁ : pw ≤ pw₁) (h₂ : A_hws pw) : A_hws pw₁ :=
begin
  cases h₂ with a h₂, use mk_A_pw_ge a h₁,
  intro d, specialize h₂ d, apply mk_A_pw_ge_wins_at_of h₂,
end