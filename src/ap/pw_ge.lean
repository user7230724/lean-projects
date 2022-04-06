import tactic.induction
import data.int.basic
import data.set.basic

import .base .player .game

noncomputable theory
open_locale classical

def mk_A_pw_ge {pw pw₁ : ℕ} (a : A pw)
  (h₁ : pw ≤ pw₁) : A pw₁ :=
begin
  refine ⟨λ s hs h, _⟩,
  refine dite (A_has_valid_move pw s.board) (λ h₂, _) (λ h₂, _),
  { have v := a.f s hs h₂, refine ⟨v.1, v.2.1, v.2.2.1.trans h₁, v.2.2.2⟩ },
  { refine ⟨_, h.some_spec⟩ },
end

lemma sup_mk_A_pw_ge {pw pw₁ : ℕ} {a : A pw}
  {h : pw ≤ pw₁} :
  (mk_A_pw_ge a h).sup a :=
begin
  rintro s hs h₁, have h₂ := A_has_valid_move_ge_of h h₁,
  use [hs, h₂], simp_rw [mk_A_pw_ge, dif_pos h₁],
end

lemma A_has_valid_move_of_exi_sub {pw pw₁ : ℕ}
  {a₁ : A pw₁} {b : Board}
  (h₁ : ∃ (a : A pw), a.sub a₁)
  (h₂ : A_has_valid_move pw b) :
  A_has_valid_move pw₁ b :=
(h₁.some_spec (init_state b) trivial ⟨_, h₂.some_spec⟩).some_spec.some

lemma sup_A_play_A_move_at_eq {pw pw₁ pw₂ : ℕ}
  {g : Game pw} {a₁ : A pw₁} {a₂ : A pw₂} {hs : g.act}
  (h₁ : a₂.sup a₁)
  (h₂ : A_has_valid_move pw₁ g.s.board) :
  ∃ h₃, play_A_move_at' a₂ g hs h₃ = play_A_move_at' a₁ g hs h₂ :=
begin
  obtain ⟨hs, h₃, h₅⟩ := h₁ g.s hs h₂, use h₃,
  simp_rw play_A_move_at', congr',
end

lemma sup_A_play_eq {pw pw₁ n : ℕ}
  {g : Game pw} {a₁ : A pw₁}
  (h₁ : g.A_wins)
  (h₂ : a₁.sup g.a) :
  (g.set_A a₁).play n = (g.play n).set_A a₁ :=
begin
  let a := g.a, let d := g.d,
  induction n with n ih, { refl },
  simp_rw play_at_succ',
  rw ih, clear ih,
  let g₁ := _, change g.play n with g₁,
  have wins_at_g₁ : g₁.A_wins := A_wins_at_play_of h₁,
  have hvm_pw₁_of : ∀ {b : Board}, A_has_valid_move pw b →
    A_has_valid_move pw₁ b := λ b, A_has_valid_move_of_exi_sub ⟨_, h₂⟩,
  have act_g₁ : g₁.act := h₁ n,
  have act_g₁_a₁ : (g₁.set_A a₁).act := h₁ n,
  rw play_move_at_act act_g₁,
  rw play_move_at_act act_g₁_a₁,
  simp_rw play_D_move_at_set_A,
  let g₂ := _, change play_D_move_at g₁ act_g₁ with g₂,
  have hvm_pw : A_has_valid_move pw g₂.s.board,
  { exact A_has_valid_move_at_play_D_move wins_at_g₁ },
  have hvm_pw₁ : A_has_valid_move pw₁ g₂.s.board,
  { exact hvm_pw₁_of hvm_pw },
  have hvm_pw' : A_has_valid_move pw (g₂.set_A a₁).s.board,
  { exact hvm_pw },
  have hvm_pw₁' : A_has_valid_move pw₁ (g₂.set_A a₁).s.board,
  { exact hvm_pw₁ },
  have act_g₂ : g₂.act := act_g₁,
  have act_g₂_a₁ : (g₂.set_A a₁).act := act_g₂,
  rw (play_A_move_hvm act_g₂ hvm_pw).some_spec,
  change play_A_move_at (g₂.set_A a₁) = _,
  rw (play_A_move_hvm act_g₂_a₁ hvm_pw₁').some_spec,
  generalize_proofs,
  change (g₂.set_A a₁).a with a₁,
  have g₁_a_eq : g₁.a = a := play_at_players_eq.1,
  have g₂_a_eq : g₂.a = a,
  { convert_to g₂.a = g₁.a, { exact g₁_a_eq.symm },
    exact play_D_move_at_players_eq.1 },
  rw g₂_a_eq,
  have h₃ : play_A_move_at' a₁ (g₂.set_A a₁) act_g₂_a₁ hvm_pw₁ =
    play_A_move_at' a (g₂.set_A a₁) act_g₂_a₁ hvm_pw',
  { exact (sup_A_play_A_move_at_eq h₂ _).some_spec },
  rw h₃, refl,
end

lemma mk_A_pw_ge_wins_at_of {pw pw₁ : ℕ}
  {g : Game pw} {h₁ : pw ≤ pw₁}
  (h₂ : g.A_wins) :
  (g.set_A (mk_A_pw_ge g.a h₁)).A_wins :=
by { intro n, rw (sup_A_play_eq h₂) sup_mk_A_pw_ge, exact h₂ n }