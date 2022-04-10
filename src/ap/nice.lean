import tactic
import tactic.induction

import .base .lemma_2_1

noncomputable theory
open_locale classical

def A_trapped_in (pw : ℕ) (s : State) (B : set Point) :=
∀ (a : A pw) (d : D) (n : ℕ), ((init_game a d s).play n).s.board.A ∈ B

def A_trapped (pw : ℕ) (s : State) :=
∃ (B : set Point), A_trapped_in pw s B

def D.nice (d : D) (pw : ℕ) :=
∀ (s : State) (hs : s.act) (p : Point) (b : Board),
¬A_trapped pw s →
(d.f s hs).m = some p →
b ∈ s.history →
pw < dist p b.A

-----

lemma lem_2_3 {pw : ℕ}
  (h : ∃ (N : ℕ) (d : D), d.nice pw ∧
  ∀ (a : A pw), A_trapped_in_for a d (Bounded N)) :
  ∃ (d : D), d.nice pw ∧ ∀ (a : A pw), (init_game a d state₀).D_wins :=
begin
  rcases h with ⟨N, d₀, h₁, h₂⟩,
  let B : set Point := _,
  change Bounded N with B at h₂,
  let d : D,
  {
    refine ⟨λ s hs, _⟩,
    apply dite (A_trapped_in pw s B); intro h,
    {
      apply dite (∃ (md : Valid_D_move s.board) (p : Point),
        md.m = some p ∧ p ∈ B); intro h₃,
      {
        exact h₃.some,
      },
      {
        exact default,
      },
    },
    {
      exact d₀.f s hs,
    },
  },
  use d,
  fsplit,
  sorry;{
    rintro s hs p b h₃ h₄ h₅,
    change Valid_D_move.m (dite _ _ _) = _ at h₄,
    split_ifs at h₄ with h₆,
    {
      rw A_trapped at h₃,
      have hh := h₃,
      push_neg at hh,
      specialize hh B,
      contradiction,
    },
    {
      cases h₄,
    },
    {
      apply h₁; assumption,
    },
  },
  {
    rintro a,
    sorry
  },
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