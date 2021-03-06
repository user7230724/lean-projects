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

lemma mem_bounded_apply_D_move_of_A_trapped_in {pw N : ℕ}
  {s : State} {md : D_move}
  (h : A_trapped_in pw s N) :
  (apply_D_move s md).board.A ∈ bounded N :=
by { rw apply_D_move_A_eq, exact mem_bounded_of_A_trapped_in h }

lemma mem_bounded_apply_A_move_of_A_trapped_in {pw N : ℕ}
  {s s' : State} {ma : Valid_A_move pw s'.board} {md : Valid_D_move s.board}
  (h₁ : A_trapped_in pw s N)
  (h₂ : s' = apply_D_move s md.m) :
  (apply_A_move s' ma.m).board.A ∈ bounded N :=
begin
  specialize h₁ ((default : A pw).set_move s' ma) ((default : D).set_move s md) 1,
  rw play_1 at h₁,
  rw Game.play_move at h₁,
  split_ifs at h₁ with h₃,
  {
    rw play_A_move_at at h₁,
    rw dif_pos at h₁, swap,
    {
      clear h₁,
      use h₃,
      subst s',
      use ma.m,
      revert h₃,
      simp,
      intro h₃,
      generalize_proofs,
      sorry,
      -- rw (_ : (init_game _ _ _).s = s),
    },
    sorry,
  },
  sorry,
end

#exit

lemma squares_in_bounded_exc_A_lt_bounded_area_of_A_trapped_in
  {pw N : ℕ} {s : State}
  (h : A_trapped_in pw s N) :
  squares_in_bounded_exc_A s.board N < bounded_area N :=
begin
  have h₃ := mem_bounded_of_A_trapped_in h,
  rw [squares_in_bounded_exc_A, bounded_area],
  apply finset.card_lt_card, rw finset.ssubset_iff,
  use s.board.A, fsplit,
  { simp },
  { rintro p hp, rw finset.mem_insert at hp,
    rw set.mem_to_finset, cases hp,
    { subst p, exact h₃ },
    { rw [finset.mem_filter, set.mem_to_finset] at hp, exact hp.1 }},
end

lemma A_trapped_in_play_move {pw N : ℕ} {g : Game pw}
  (h : A_trapped_in pw g.s N) :
  A_trapped_in pw g.play_move.s N :=
begin
  sorry
end

lemma nice_D_wins_upper_bound_of_A_trapped_in {pw N : ℕ}
  {a : A pw} {d : D} {s₀ : State}
  (h₀ : valid_state pw s₀)
  (h₁ : d.nice pw)
  (h₂ : A_trapped_in pw s₀ N) :
  ¬((init_game a d s₀).play (bounded_area N)).act :=
begin
  apply not_act_of_descend_play_move_valid
    (λ (s : State), squares_in_bounded_exc_A s.board N)
    (λ (s : State), A_trapped_in pw s N); try { dsimp },
  sorry {
    exact h₀,
  },
  sorry {
    exact squares_in_bounded_exc_A_lt_bounded_area_of_A_trapped_in h₂,
  },
  sorry {
    exact h₂,
  },
  sorry {
    rintro s hv hs₁ h₃,
    exact A_trapped_in_play_move h₃,
  },
  {
    rintro s hv hs₁ h₃,
    obtain ⟨s', hs, hs', hvm, h₄, h₅⟩ := play_move_state_eq_of_act_play_move hs₁,
    rw h₅, clear h₅,
    simp only [init_game_a_eq, init_game_d_eq, init_game_s_eq] at *,
    rw (_ : squares_in_bounded_exc_A (apply_A_move _ _).board N =
      squares_in_bounded_exc_A s'.board N), swap,
    {
      simp_rw squares_in_bounded_exc_A,
      let ma : Valid_A_move pw s'.board := _,
      change (a.f s' hs' hvm) with ma,
      let t : finset Point := _,
      change _ = t.card,
      have hma₁ : ma.m ∈ bounded N,
      {
        sorry
      },
      have hma₂ : ma.m ∈ s'.board.squares,
      sorry,
      have hma₃ : ma.m ≠ s'.board.A,
      sorry,
      have h₅ : ma.m ∈ t,
      sorry {
        rw [finset.mem_filter, set.mem_to_finset],
        exact ⟨hma₁, hma₂, hma₃⟩,
      },
      have h₆ : s'.board.A ∉ t,
      sorry {
        rw finset.mem_filter,
        simp,
      },
      convert finset_card_insert_erase_eq h₅ h₆,
      ext p,
      simp_rw [finset.mem_filter, finset.mem_insert,
        set.mem_to_finset, finset.mem_erase],
      change (apply_A_move s' ma.m).board.A with ma.m,
      change (apply_A_move s' ma.m).board.squares with s'.board.squares,
      by_cases h₇ : p = ma.m,
      sorry {
        subst p,
        simp,
        exact ma.h.1,
      },
      {
        simp only [true_and, and_true, set.mem_to_finset, ne.def, not_false_iff,
          finset.mem_filter, h₇],
        split; intro h₈,
        sorry {
          tauto,
        },
        {
          change _ ≠ _ at h₇,
          cases h₈,
          {
            clear h₇,
            subst h₈,
            fsplit,
            sorry {
              subst s',
              exact mem_bounded_apply_D_move_of_A_trapped_in h₃,
            },
            {
              sorry -- valid_state pw s
            },
          },
          sorry {
            tauto,
          },
        },
      },
    },
    sorry -- because nice D eats one non-A square from `Bounded N`
  },
end

#exit

lemma nice_D_wins_of_can_entrap_in {pw N : ℕ} {a : A pw} {d : D}
  (h₁ : d.nice pw)
  (h₂ : can_entrap_in a d N) :
  (init_game a d state₀).D_wins :=
begin
  cases h₂ with n h₂, suffices h₃ : ∃ (k : ℕ), ¬(simulate a d (n + k)).act,
  { exact ⟨_, h₃.some_spec⟩ },
  simp_rw simulate_add,let g : Game pw := _,
  change simulate a d n with g at h₂ ⊢, split,
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
  rcases h with ⟨N, d, h₁, h₂⟩, use [d, h₁], intro a,
  specialize h₂ a, exact nice_D_wins_of_can_entrap_in h₁ h₂,
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
      rw add_assoc at h, rw [simulate, play_add] at h, apply act_of_act_play h },
    have h₄ : simulate a d k = simulate a d n,
    { exact play_eq_of_not_act h₃ h },
    rw h₄, apply A_bounded_n_pw, refl },
end