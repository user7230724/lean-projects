import tactic
import tactic.induction

import .base .bounded .determinacy .induct

noncomputable theory
open_locale classical

def A_trapped_in_for {pw : ℕ} (a : A pw) (d : D) (B : set Point) :=
all_b a d (λ b, b.A ∈ B)

lemma exi_ma_inf_n_of_exi_A {pw : ℕ} {d : D} {s s' : State} {hs}
  (h₁ : ∀ (n : ℕ), ∃ (a : A pw), ((init_game a d s).play n).act)
  (h₂ : s' = apply_D_move s (d.f s hs).m) :
  ∃ (ma : Valid_A_move pw s'.board),
  {n : ℕ | ∃ (a : A pw) hs' hvm, a.f s' hs' hvm = ma ∧
  ((init_game a d s).play n).act}.infinite :=
begin
  fapply exi_set_infinite_of_forall_exi_P_nat, rintro n,
  obtain ⟨a, h₃⟩ := h₁ n, obtain ⟨a₁, h₄⟩ := h₁ 1, have hs' : s'.act,
  { subst h₂, assumption },
  have hvm : A_has_valid_move pw s'.board,
  { rw [play_1, play_move_at_act] at h₄, swap, { assumption },
    have h₅ : play_D_move_at (init_game a₁ d s) hs = init_game a₁ d s',
    { subst h₂, refl },
    rw [h₅, play_A_move_at] at h₄, clear h₅, split_ifs at h₄ with h₅,
    { exact h₅.2 },
    { cases h₄ }},
  exact ⟨a.f s' hs' hvm, a, hs', hvm, rfl, h₃⟩,
end

lemma exi_A_forall_n_play_act_of_swap {pw : ℕ} {d : D} {s : State}
  (h : ∀ (n : ℕ), ∃ (a : A pw), ((init_game a d s).play n).act) :
  ∃ (a : A pw), ∀ (n : ℕ), ((init_game a d s).play n).act :=
begin
  apply @exi_A_wins_of_invariant (λ s, ∀ (n : ℕ), ∃ (a : A pw),
    ((init_game a d s).play n).act); assumption <|> clear h; dsimp,
  { rintro s h₁, specialize h₁ 0, exact h₁.some_spec },
  { rintro s s' hs h₁ h₂, obtain ⟨ma, hma⟩ := exi_ma_inf_n_of_exi_A h₁ h₂,
    use ma, rintro n, obtain ⟨k, h₃, a, hs', hvm, hh, h₄⟩ := exi_ge_of_set_inf hma,
    use a, convert_to ((init_game a d s).play (n + 1)).act,
    { rw [play_add', play_1], congr, symmetry, ext,
      { exact play_move_at_players_eq.1 },
      { exact play_move_at_players_eq.2 },
      { have h₅ := act_of_act_play h₄, rw play_move_at_act h₅,
        have h₆ : play_D_move_at (init_game a d s) h₅ = init_game a d s',
        { ext; try { refl }, exact h₂.symm },
        rw [h₆, play_A_move_at, dif_pos], clear h₆, swap, { exact ⟨hs', hvm⟩ },
        change apply_A_move s' (a.f s' _ _).m = apply_A_move s' ma.m, congr' }},
    exact act_play_le h₃ h₄ },
end

lemma D_wins_n_of_D_hws {pw : ℕ}
  (h : D_hws pw) :
  ∃ (n : ℕ) (d : D), ∀ (a : A pw),
  D_wins_in a d n :=
begin
  contrapose! h, rw forall_swap at h, change ∀ (d : D) (n : ℕ), _ at h,
  simp_rw [D_wins_in, simulate] at h, push_neg at h, rw [D_hws, D_hws_at],
  push_neg, intro d, specialize h d,
  replace h : ∀ (n : ℕ), ∃ (a : A pw), ((init_game a d state₀).play n).act,
  { intro n, specialize h n, cases h with a h, use a, rcases h with ⟨k, h₁, h₂⟩,
    obtain ⟨k, rfl⟩ := nat.exists_eq_add_of_le h₁, apply act_play_le h₁ h₂ },
  simp_rw Game.D_wins, push_neg, exact exi_A_forall_n_play_act_of_swap h,
end

lemma A_bounded_n_pw {pw n k : ℕ} {a : A pw} {d : D}
  (h : k ≤ n) :
  (simulate a d k).s.board.A ∈ bounded (n * pw) :=
begin
  induction k with k ih generalizing n,
  { apply nat.zero_le },
  { rw simulate at ih ⊢, rw play_at_succ',
    let g₁ : Game pw := _, change (init_game a d state₀).play k with g₁ at ih ⊢,
    rw Game.play_move, split_ifs with h₁, swap, { exact ih (nat.le_of_succ_le h) },
    rw play_A_move_at, split_ifs with h₂,
    { let s' := (play_D_move_at g₁ h₁).s,
      change (apply_A_move_b s'.board (g₁.a.f _ _ _).m).A ∈ _,
      rw apply_A_move_b, dsimp, generalize_proofs h₃,
      let ma := g₁.a.f s' h₁ h₃, change ma.m ∈ _, have h₄ := ma.h.2.1,
      have h₅ : s'.board.A = g₁.s.board.A := apply_D_move_A_eq,
      rw h₅ at h₄, clear h₅, cases n, { cases h }, rw nat.succ_le_succ_iff at h,
      specialize ih h, change _ ≤ _ at ih, change _ ≤ _, rw nat.succ_mul,
      transitivity dist ma.m g₁.s.board.A + dist g₁.s.board.A center,
      { exact dist_triangle },
      { rw add_comm, exact add_le_add ih h₄ }},
    { have h₃ : (play_D_move_at g₁ h₁).finish.s.board.A = g₁.s.board.A,
      { exact apply_D_move_A_eq },
      rw h₃, exact ih (nat.le_of_succ_le h) }},
end

lemma lem_2_1 {pw : ℕ}
  (h : D_hws pw) :
  ∃ (N : ℕ) (d : D), ∀ (a : A pw),
  A_trapped_in_for a d (bounded N) :=
begin
  obtain ⟨n, d, h₁⟩ := D_wins_n_of_D_hws h,
  use [n * pw, d], intro a, specialize h₁ a, intro k,
  have h₂ := h₁ _ (le_refl _), by_cases h₃ : n ≤ k,
  { have h₄ := h₁ _ h₃, have h₅ := simulate_eq_of_not_act h₄ h₂,
    rw h₅, clear' k h₁ h₂ h₃ h₄ h₅, exact A_bounded_n_pw (le_refl _) },
  { push_neg at h₃, exact A_bounded_n_pw (le_of_lt h₃) },
end