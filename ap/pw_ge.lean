import tactic.induction
import data.int.basic
import data.set.basic

import .player .game

noncomputable theory
open_locale classical

def mk_angel_pw_ge {pw pw₁ : ℕ} (a : Angel pw)
  (h₁ : pw ≤ pw₁) : Angel pw₁ :=
begin
  refine ⟨λ s hs h, _⟩,
  refine dite (angel_has_valid_move pw s.board) (λ h₂, _) (λ h₂, _),
  { have v := a.f s hs h₂, refine ⟨v.1, v.2.1, v.2.2.1.trans h₁, v.2.2.2⟩ },
  { refine ⟨_, h.some_spec⟩ },
end

lemma sup_mk_angel_pw_ge {pw pw₁ : ℕ} {a : Angel pw}
  {h : pw ≤ pw₁} :
  (mk_angel_pw_ge a h).sup a :=
begin
  rintro s hs h₁, have h₂ := angel_has_valid_move_ge_of h h₁,
  use [hs, h₂], simp_rw [mk_angel_pw_ge, dif_pos h₁],
end

lemma angel_has_valid_move_of_exi_sub {pw pw₁ : ℕ}
  {a₁ : Angel pw₁} {b : Board}
  (h₁ : ∃ (a : Angel pw), a.sub a₁)
  (h₂ : angel_has_valid_move pw b) :
  angel_has_valid_move pw₁ b :=
(h₁.some_spec (init_state b) trivial ⟨_, h₂.some_spec⟩).some_spec.some

lemma sup_angel_play_angel_move_at_eq {pw pw₁ pw₂ : ℕ}
  {g : Game pw} {a₁ : Angel pw₁} {a₂ : Angel pw₂} {hs : g.act}
  (h₁ : a₂.sup a₁)
  (h₂ : angel_has_valid_move pw₁ g.s.board) :
  ∃ h₃, play_angel_move_at' a₂ g hs h₃ = play_angel_move_at' a₁ g hs h₂ :=
begin
  obtain ⟨hs, h₃, h₅⟩ := h₁ g.s hs h₂, use h₃,
  simp_rw play_angel_move_at', congr',
end

lemma sup_angel_play_eq {pw pw₁ n : ℕ}
  {g : Game pw} {a₁ : Angel pw₁}
  (h₁ : g.angel_wins)
  (h₂ : a₁.sup g.a) :
  (g.set_angel a₁).play n = (g.play n).set_angel a₁ :=
begin
  let a := g.a, let d := g.d,
  induction n with n ih, { refl },
  simp_rw play_at_succ',
  rw ih, clear ih,
  let g₁ := _, change g.play n with g₁,
  have wins_at_g₁ : g₁.angel_wins := angel_wins_at_play_of h₁,
  have hvm_pw₁_of : ∀ {b : Board}, angel_has_valid_move pw b →
    angel_has_valid_move pw₁ b := λ b, angel_has_valid_move_of_exi_sub ⟨_, h₂⟩,
  have act_g₁ : g₁.act := h₁ n,
  have act_g₁_a₁ : (g₁.set_angel a₁).act := h₁ n,
  rw play_move_at_act act_g₁,
  rw play_move_at_act act_g₁_a₁,
  simp_rw play_devil_move_at_set_angel,
  let g₂ := _, change play_devil_move_at g₁ act_g₁ with g₂,
  have hvm_pw : angel_has_valid_move pw g₂.s.board,
  { exact angel_has_valid_move_at_play_devil_move wins_at_g₁ },
  have hvm_pw₁ : angel_has_valid_move pw₁ g₂.s.board,
  { exact hvm_pw₁_of hvm_pw },
  have hvm_pw' : angel_has_valid_move pw (g₂.set_angel a₁).s.board,
  { exact hvm_pw },
  have hvm_pw₁' : angel_has_valid_move pw₁ (g₂.set_angel a₁).s.board,
  { exact hvm_pw₁ },
  have act_g₂ : g₂.act := act_g₁,
  have act_g₂_a₁ : (g₂.set_angel a₁).act := act_g₂,
  rw (play_angel_move_hvm act_g₂ hvm_pw).some_spec,
  change play_angel_move_at (g₂.set_angel a₁) = _,
  rw (play_angel_move_hvm act_g₂_a₁ hvm_pw₁').some_spec,
  generalize_proofs,
  change (g₂.set_angel a₁).a with a₁,
  have g₁_a_eq : g₁.a = a := play_at_players_eq.1,
  have g₂_a_eq : g₂.a = a,
  { convert_to g₂.a = g₁.a, { exact g₁_a_eq.symm },
    exact play_devil_move_at_players_eq.1 },
  rw g₂_a_eq,
  have h₃ : play_angel_move_at' a₁ (g₂.set_angel a₁) act_g₂_a₁ hvm_pw₁ =
    play_angel_move_at' a (g₂.set_angel a₁) act_g₂_a₁ hvm_pw',
  { exact (sup_angel_play_angel_move_at_eq h₂ _).some_spec },
  rw h₃, refl,
end

lemma mk_angel_pw_ge_wins_at_of {pw pw₁ : ℕ}
  {g : Game pw} {h₁ : pw ≤ pw₁}
  (h₂ : g.angel_wins) :
  (g.set_angel (mk_angel_pw_ge g.a h₁)).angel_wins :=
by { intro n, rw (sup_angel_play_eq h₂) sup_mk_angel_pw_ge, exact h₂ n }