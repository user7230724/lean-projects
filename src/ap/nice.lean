import tactic
import tactic.induction

import .base .bounded .lemma_2_1

noncomputable theory
open_locale classical

def A_trapped_in (pw : ℕ) (s : State) (N : ℕ) :=
∀ (a : A pw) (d : D) (n : ℕ), ((init_game a d s).play n).s.board.A ∈ bounded N

def A_trapped (pw : ℕ) (s : State) :=
∃ (N : ℕ), A_trapped_in pw s N

def can_entrap_in {pw : ℕ} (a : A pw) (d : D) (N : ℕ) :=
∃ (n : ℕ), A_trapped_in pw (simulate a d n).s N

def D_nice_cond (pw : ℕ) (s : State) (n : ℕ) : Prop :=
A_trapped_in pw s n ∧ ∃ (md : Valid_D_move s.board) (p : Point),
md.m = some p ∧ p ∈ bounded n

def D.nice (d : D) (pw : ℕ) :=
∀ (s : State) (hs : s.act) (N : ℕ),
if D_nice_cond pw s N
then ∃ (p : Point),
  (d.f s hs).m = some p ∧
  p ∈ bounded N
else ∀ (p : Point) (b : Board),
  (d.f s hs).m = some p →
  b ∈ s.history →
  pw < dist p b.A

-----

lemma A_trapped_in_ge {pw n k : ℕ} {s : State}
  (h₁ : A_trapped_in pw s k)
  (h₂ : k ≤ n) :
  A_trapped_in pw s n :=
λ a d m, mem_bounded_ge (h₁ a d m) h₂

lemma can_entrap_in_ge {pw n k : ℕ} {a : A pw} {d : D}
  (h₁ : can_entrap_in a d k)
  (h₂ : k ≤ n) :
  can_entrap_in a d n :=
⟨_, A_trapped_in_ge h₁.some_spec h₂⟩

lemma D_nice_cond_ge {pw n k : ℕ} {s : State}
  (h₁ : D_nice_cond pw s k)
  (h₂ : k ≤ n) :
  D_nice_cond pw s n :=
begin
  obtain ⟨md, p, h₃, h₄⟩ := h₁.2,
  exact ⟨A_trapped_in_ge h₁.1 h₂, _, _, h₃, mem_bounded_ge h₄ h₂⟩,
end

lemma mem_bounded_of_A_trapped_in {pw N : ℕ} {s : State}
  (h : A_trapped_in pw s N) :
  s.board.A ∈ bounded N :=
h default default 0

lemma A_trapped_in_play_move {pw N : ℕ} {g : Game pw}
  (h : A_trapped_in pw g.s N) :
  A_trapped_in pw g.play_move.s N :=
begin
  sorry
end

lemma nice_D_wins_upper_bound_of_A_trapped_in {pw N : ℕ}
  {a : A pw} {d : D} {s₀ : State}
  (h₁ : d.nice pw)
  (h₂ : A_trapped_in pw s₀ N) :
  ¬((init_game a d s₀).play (bounded_area N)).act :=
begin
  apply not_act_of_descend_play_move
    (λ (s : State), squares_in_bounded_exc_A s.board N)
    (λ (s : State), A_trapped_in pw s N); try { dsimp },
  sorry { have h₃ := mem_bounded_of_A_trapped_in h₂,
    rw [squares_in_bounded_exc_A, bounded_area],
    apply finset.card_lt_card, rw finset.ssubset_iff,
    use s₀.board.A, fsplit,
    { simp },
    { rintro p hp, rw finset.mem_insert at hp,
      rw set.mem_to_finset, cases hp,
      { subst p, exact h₃ },
      { rw [finset.mem_filter, set.mem_to_finset] at hp, exact hp.1 }}},
  sorry {
    exact h₂,
  },
  {
    rintro g hs₁ h₃,
    exact A_trapped_in_play_move h₃,
  },
  {
    -- See notes in `not_act_of_descend_play_move` from `induct.lean`
    rintro g hs₁ h₃,
    have h₄ := A_trapped_in_play_move h₃,
    apply finset.card_lt_card,
    simp [finset.ssubset_iff],
    obtain ⟨s, s', hs, hs', hvm, h₅⟩ :=
      play_move_state_eq_of_act_play_move hs₁,
    use option.iget (g.d.f g.s s').m,
    clear' s₀ h₂,
    sorry
    -- have ha : g.a = a := play_at_players_eq.1, rw ha at *, clear ha,
    -- have hd : g.d = d := play_at_players_eq.2, rw ha at *, clear ha,
    -- split,
    -- {
    --   extract_goal,
    -- },
    -- sorry,
  },
end

#exit

lemma nice_D_wins_of_can_entrap_in {pw N : ℕ} {a : A pw} {d : D}
  (h₁ : d.nice pw)
  (h₂ : can_entrap_in a d N) :
  (init_game a d state₀).D_wins :=
begin
  cases h₂ with n h₂,
  suffices h₃ : ∃ (k : ℕ), ¬(simulate a d (n + k)).act,
  { exact ⟨_, h₃.some_spec⟩ },
  simp_rw simulate_add,let g : Game pw := _,
  change simulate a d n with g at h₂ ⊢,
  split,
  rw (_ : g = init_game a d g.s), swap,
  { ext,
    { exact play_at_players_eq.1 },
    { exact play_at_players_eq.2 },
    { refl }},
  exact nice_D_wins_upper_bound_of_A_trapped_in h₁ h₂,
end

lemma lem_2_3 {pw : ℕ}
  (h : ∃ (N : ℕ) (d : D), d.nice pw ∧ ∀ (a : A pw), can_entrap_in a d N) :
  ∃ (d : D), d.nice pw ∧ ∀ (a : A pw), (init_game a d state₀).D_wins :=
begin
  rcases h with ⟨N, d, h₁, h₂⟩,
  use [d, h₁],
  intro a,
  specialize h₂ a,
  exact nice_D_wins_of_can_entrap_in h₁ h₂,
end

lemma lem_2_3' {pw : ℕ}
  (h : ∃ (a : A pw), ∀ (d : D) (N : ℕ), d.nice pw →
  ¬A_trapped_in_for a d (bounded N)) :
  ∃ (a : A pw), ∀ (d : D), d.nice pw → (init_game a d state₀).A_wins :=
begin
  cases h with a h, use a, rintro d h₁, specialize h d,
  replace h : ∀ (N : ℕ), ¬A_trapped_in_for a d (bounded N),
  { intro n, exact h n h₁ },
  intro n, contrapose! h, use n * pw, intro k, by_cases h₂ : k ≤ n,
  { exact A_bounded_n_pw h₂ },
  { change ¬(simulate a d n).act at h, have h₃ : ¬(simulate a d k).act,
    { contrapose! h, push_neg at h₂, obtain ⟨k, rfl⟩ := nat.exists_eq_add_of_lt h₂,
      rw add_assoc at h, rw [simulate, play_add] at h, apply act_of_play_act h },
    have h₄ : simulate a d k = simulate a d n,
    { exact play_eq_of_not_act h₃ h },
    rw h₄, apply A_bounded_n_pw, refl },
end