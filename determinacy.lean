import tactic.induction
import data.int.basic
import data.set.basic
import logic.function.iterate

import .game

noncomputable theory
open_locale classical

lemma not_angel_hws_at_of {pw : ℕ} {s : State}
  (h : devil_hws_at pw s) : ¬angel_hws_at pw s :=
begin
  cases h with d h, change ¬∃ _, _, push_neg,
  intro a, use d, rw not_angel_wins_at, apply h,
end

lemma not_devil_hws_at_of {pw : ℕ} {s : State}
  (h : angel_hws_at pw s) : ¬devil_hws_at pw s :=
begin
  cases h with d h, change ¬∃ _, _, push_neg,
  intro a, use d, rw not_devil_wins_at, apply h,
end

-----

lemma exi_angel_move_of_not_devil_hws_at {pw : ℕ} {s : State}
  (h : ¬devil_hws_at pw s) :
  ∀ (md : Valid_devil_move s.board),
  ∃ (ma : Valid_angel_move pw (apply_devil_move s md.m).board),
  ¬devil_hws_at pw (apply_angel_move (apply_devil_move s md.m) ma.m) :=
begin
  sorry
end

def mk_angel_st_for_not_devil_hws_at (pw : ℕ) : Angel pw :=
begin
  refine ⟨λ s' h, _⟩,
  apply dite (∃ (s : State) (md : Valid_devil_move s.board),
    ¬devil_hws_at pw s ∧ s' = apply_devil_move s md.m);
  intro h₁,
  { refine (_ : nonempty _).some, rcases h₁ with ⟨s, md, h₁, rfl⟩,
    use (exi_angel_move_of_not_devil_hws_at h₁ md).some },
  { exact ⟨_, h.some_spec⟩ },
end

lemma angel_hws_at_of {pw : ℕ} {s : State}
  (h : ¬devil_hws_at pw s) : angel_hws_at pw s :=
begin
  use mk_angel_st_for_not_devil_hws_at pw,
  rintro d n,
  let g : Game pw := _, change (g.play n).act,
  suffices h₁ : (g.play n).act ∧ ¬devil_hws_at pw (g.play n).s, { exact h₁.1 },
  induction n with n ih,
  { exact ⟨trivial, h⟩ },
  {
    rw play_at_succ',
    let g₁ : Game pw := _, change g.play n with g₁ at ih ⊢,
    cases ih with ih₁ ih₂,
    fsplit,
    sorry,
    {
      change ¬∃ _, _, push_neg, intro d,
      obtain ⟨ma, h₁⟩ := exi_angel_move_of_not_devil_hws_at ih₂ (d.f _),
      change ¬∃ _, _ at h₁, push_neg at h₁,
      specialize h₁ d,
      cases h₁ with a h₁,

      let s' : State := _,
      change apply_devil_move g₁.s (d.f g₁.s).m with s' at ma h₁,
      use a.modify_move s' ma,

      -- convert h₁, clear h₁,
      -- rw play_move_at_act ih₁,

      -- let g₂ : Game pw := _, change play_devil_move_at g₁ with g₂,
      -- have h₁ : apply_devil_move g₁.s (d.f g₁.s).m = g₂.s,
      -- sorry,
      -- simp_rw h₁,

      -- have hvm : angel_has_valid_move pw g₂.s.board,
      -- {
      --   have ma' := ma,
      --   rw h₁ at ma',
      --   sorry
      -- },

      -- rw [play_angel_move_at, dif_pos hvm, play_angel_move_at'], dsimp,
      -- congr' 1,
    },
  },
end

#exit

-----

lemma devil_hws_at_of {pw : ℕ} {s : State}
  (h : ¬angel_hws_at pw s) : devil_hws_at pw s :=
by { contrapose! h, exact angel_hws_at_of h }

lemma not_angel_hws_at_iff {pw : ℕ} {s : State} :
  ¬angel_hws_at pw s ↔ devil_hws_at pw s :=
⟨devil_hws_at_of, not_angel_hws_at_of⟩

lemma not_devil_hws_at_iff {pw : ℕ} {s : State} :
  ¬devil_hws_at pw s ↔ angel_hws_at pw s :=
⟨angel_hws_at_of, not_devil_hws_at_of⟩