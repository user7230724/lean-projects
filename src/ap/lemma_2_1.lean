import tactic
import tactic.induction

import .base .determinacy .induct

noncomputable theory
open_locale classical

def D_hws (pw : ℕ) := D_hws_at pw state₀

def D_wins_in {pw : ℕ} (a : A pw) (d : D) (n : ℕ) :=
∀ (k : ℕ), n ≤ k → ¬(simulate a d k).act

def Bounded (r : ℕ) : set Point :=
{p : Point | dist p center ≤ r}

def trapped_in {pw : ℕ} (a : A pw) (d : D) (B : set Point) :=
all_b a d (λ b, b.A ∈ B)

def mk_A_for_lem_2_1 (pw : ℕ) (d : D) : A pw := ⟨λ s' hs' hvm,
if h : ∃ ma s₁, ∀ (n : ℕ), ∃ (a : A pw),
  ((init_game a d s₁).play n).act ∧ a.f s' hs' hvm = ma
then h.some
else ⟨_, hvm.some_spec⟩⟩

lemma exi_A_forall_n_play_act_of_swap {pw : ℕ} {s₀ : State} {d : D}
  (h : ∀ (n : ℕ), ∃ (a : A pw), ((init_game a d s₀).play n).act) :
  ∃ (a : A pw), ∀ (n : ℕ), ((init_game a d s₀).play n).act :=
begin
  sorry
end

#exit

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
    obtain ⟨k, rfl⟩ := nat.exists_eq_add_of_le h₁, apply act_play_at_le h₁ h₂ },
  simp_rw Game.D_wins, push_neg, exact exi_A_forall_n_play_act_of_swap h,
end

#exit

lemma A_bounded_n_pw {pw n k : ℕ} {a : A pw} {d : D}
  (h : k ≤ n) :
  (simulate a d k).s.board.A ∈ Bounded (n * pw) :=
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
      have h₅ : s'.board.A = g₁.s.board.A := apply_D_move_b_A,
      rw h₅ at h₄, clear h₅, cases n, { cases h }, rw nat.succ_le_succ_iff at h,
      specialize ih h, change _ ≤ _ at ih, change _ ≤ _, rw nat.succ_mul,
      transitivity dist ma.m g₁.s.board.A + dist g₁.s.board.A center,
      { exact dist_triangle },
      { rw add_comm, exact add_le_add ih h₄ }},
    { have h₃ : (play_D_move_at g₁ h₁).finish.s.board.A = g₁.s.board.A,
      { exact apply_D_move_b_A },
      rw h₃, exact ih (nat.le_of_succ_le h) }},
end

lemma lem_2_1 {pw : ℕ}
  (h : D_hws pw) :
  ∃ (N : ℕ) (d : D), ∀ (a : A pw),
  trapped_in a d (Bounded N) :=
begin
  obtain ⟨n, d, h₁⟩ := D_wins_n_of_D_hws h,
  use [n * pw, d], intro a, specialize h₁ a, intro k,
  have h₂ := h₁ _ (le_refl _), by_cases h₃ : n ≤ k,
  { have h₄ := h₁ _ h₃, have h₅ := simulate_eq_of_not_act h₄ h₂,
    rw h₅, clear' k h₁ h₂ h₃ h₄ h₅, exact A_bounded_n_pw (le_refl _) },
  { push_neg at h₃, exact A_bounded_n_pw (le_of_lt h₃) },
end