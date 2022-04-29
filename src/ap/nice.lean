import tactic
import tactic.induction

import .base .lemma_2_1

noncomputable theory
open_locale classical

def A_trapped_in (pw : ℕ) (s : State) (N : ℕ) :=
∀ (a : A pw) (d : D) (n : ℕ), ((init_game a d s).play n).s.board.A ∈ Bounded N

def A_trapped (pw : ℕ) (s : State) :=
∃ (N : ℕ), A_trapped_in pw s N

def can_entrap_in {pw : ℕ} (a : A pw) (d : D) (N : ℕ) :=
∃ (n : ℕ), A_trapped_in pw (simulate a d n).s N

def D_nice_cond (pw : ℕ) (s : State) (n : ℕ) : Prop :=
A_trapped_in pw s n ∧ ∃ (md : Valid_D_move s.board) (p : Point),
md.m = some p ∧ p ∈ Bounded n

def D.nice (d : D) (pw : ℕ) :=
∀ (s : State) (hs : s.act) (N : ℕ),
if D_nice_cond pw s N
then ∃ (p : Point),
  (d.f s hs).m = some p ∧
  p ∈ Bounded N
else ∀ (p : Point) (b : Board),
  (d.f s hs).m = some p →
  b ∈ s.history →
  pw < dist p b.A

-----

lemma A_trapped_in_ge {pw n k : ℕ} {s : State}
  (h₁ : A_trapped_in pw s k)
  (h₂ : k ≤ n) :
  A_trapped_in pw s n :=
λ a d m, mem_Bounded_ge (h₁ a d m) h₂

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
  exact ⟨A_trapped_in_ge h₁.1 h₂, _, _, h₃, mem_Bounded_ge h₄ h₂⟩,
end

-----

def mk_D_for_lem_2_3 (pw : ℕ) (d₀ : D) : D :=
begin
  refine ⟨λ s hs, _⟩,
  apply dite (∃ (N : ℕ), A_trapped_in pw s N); intro h,
  { apply dite (∃ (p : Point),
      p ∈ s.board.squares ∧ p ∈ Bounded (nat.find h) ∧ p ≠ s.board.A); intro h₁,
    { exact ⟨some h₁.some, h₁.some_spec.2.2, h₁.some_spec.1⟩ },
    { exact default }},
  { exact d₀.f s hs },
end

lemma mk_D_for_lem_2_3_nice_of_nice {pw : ℕ} {d₀ : D}
  (h : d₀.nice pw) :
  (mk_D_for_lem_2_3 pw d₀).nice pw :=
begin
  rintro s hs N,
  split_ifs with h₁,
  {
    rw mk_D_for_lem_2_3, dsimp,
    split_ifs with h₂ h₃ h₄,
    {
      use [h₃.some, rfl],
      apply mem_Bounded_ge h₃.some_spec.2.1,
      rw nat.find_le_iff,
      use [N, le_refl _, h₁.1],
    },
    {
      contrapose! h₃, clear h₃,
      have h₃ : ∃ (N : ℕ), D_nice_cond pw s N := ⟨_, h₁⟩,
      have h₄ := nat.find_spec h₃,
      obtain ⟨md, p, h₅, h₆⟩ := h₄.2,
      use p,
      have h₇ := md.h,
      rw h₅ at h₇,
      rw D_move_valid at h₇,
      refine ⟨h₇.2, _, h₇.1⟩, clear h₇,
      apply mem_Bounded_ge h₆, clear h₆,
      change ∃ (N : ℕ), A_trapped_in pw s N at h₂,
      have h₆ := nat.find_spec h₂,
      apply nat_find_le_nat_find_of,
      rintro n hn,
      sorry
    },
    sorry,
  },
  sorry,
end

#exit

lemma lem_2_3 {pw : ℕ}
  (h : ∃ (N : ℕ) (d : D), d.nice pw ∧ ∀ (a : A pw), can_entrap_in a d N) :
  ∃ (d : D), d.nice pw ∧ ∀ (a : A pw), (init_game a d state₀).D_wins :=
begin
  rcases h with ⟨N, d, h₁, h₂⟩,


  -- use [d, h₁],
  -- rintro a,
  -- specialize h₂ a,
  -- cases h₂ with n h₂,
  -- let D := N ^ 2 + 8,
  -- use n + D,
  -- rw play_add,
  -- rw ←simulate,
  -- let g : Game pw := _,
  -- change simulate a d n with g at h₂ ⊢,
  --
  -- -- have h₃ := h₂ a d,
  -- -- have h₄ : init_game a d g.s = g,
  -- -- { symmetry, ext, exact play_at_players_eq.1, exact play_at_players_eq.2, refl },
  -- -- rw h₄ at h₃, clear h₄,
  --
  -- have h₃ : ∀ (k : ℕ), cardinal.mk {p : Point | p ∈ (g.play k).s.board.squares} = k,
  -- {
  --   sorry,
  -- },
  -- sorry
end

#exit

lemma lem_2_3' {pw : ℕ}
  (h : ∃ (a : A pw), ∀ (d : D) (N : ℕ), d.nice pw →
  ¬A_trapped_in_for a d (Bounded N)) :
  ∃ (a : A pw), ∀ (d : D), d.nice pw → (init_game a d state₀).A_wins :=
begin
  cases h with a h, use a, rintro d h₁, specialize h d,
  replace h : ∀ (N : ℕ), ¬A_trapped_in_for a d (Bounded N),
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