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

-- lemma act_of_not_devil_hvs {pw : ℕ} {g : Game pw}
--   (h : ¬devil_hws_at pw g.s) : g.act :=
-- begin
--   change ¬∃ _, _ at h, push_neg at h,
--   specialize h g.d,
--   cases h with a₁ h,
-- end

-- #exit

lemma exi_angel_move_of_not_devil_hws {pw : ℕ} {s : State}
  (h : ¬devil_hws_at pw s) :
  ∀ (md : Valid_devil_move s.board),
  ∃ (ma : Valid_angel_move pw (apply_devil_move s md.m).board),
  ¬devil_hws_at pw (apply_angel_move (apply_devil_move s md.m) ma.m) :=
begin
  sorry
end

def mk_angel_st_for_not_devil_hws (pw : ℕ) : Angel pw :=
begin
  refine ⟨λ s' h, _⟩,
  apply dite (∃ (s : State) (md : Valid_devil_move s.board),
    ¬devil_hws_at pw s ∧ s' = apply_devil_move s md.m);
  intro h₁,
  { refine (_ : nonempty _).some, rcases h₁ with ⟨s, md, h₁, rfl⟩,
    use (exi_angel_move_of_not_devil_hws h₁ md).some },
  { exact ⟨_, h.some_spec⟩ },
end

lemma angel_hws_at_of {pw : ℕ} {s : State}
  (h : ¬devil_hws_at pw s) : angel_hws_at pw s :=
begin
  use mk_angel_st_for_not_devil_hws pw,
  rintro d n,
  let g : Game pw := _, change (g.play n).act,
  suffices h₁ : ¬devil_hws_at pw (g.play n).s ∧ _, exact h₁.2,
  induction n with n ih,
  { exact ⟨h, trivial⟩ },
  {
    rw play_at_succ',
    let g₁ : Game pw := _, change g.play n with g₁ at ih ⊢,
    cases ih with ih₁ ih₂,
    have hh := exi_angel_move_of_not_devil_hws ih₁,
    fsplit,
    {
      have ih' := ih₁,
      change ¬∃ _, _ at ih', push_neg at ih',
      change ¬∃ _, _, push_neg,
      intro d',
      specialize ih' d',
      cases ih' with a' ih',
      simp_rw not_devil_wins_at at ih' ⊢,
      use a',
      intro k,
      specialize ih' k.succ,
      rw play_at_succ at ih',
      convert ih',
      symmetry,
      have h₁ : (⟨a', d, g₁.s, true⟩ : Game _) = g₁,
      {
        ext,
        {
          sorry
        },
        sorry,
        sorry,
        sorry,
      },
      sorry
      -- have h₂ : g₁.play_move = g₁.set_state g₁.play_move.s,
      -- {
      --   clear h₁,
      --   apply play_move_eq_set_state_of_act_next,
      --   rw play_move_at_act ih₂,
      --   let g₁' : Game pw := _, change play_devil_move_at g₁ with g₁',
      --   change Game.act (dite _ _ _),
      --   split_ifs with h₁,
      --   {
      --     exact ih₂,
      --   },
      --   {
      --     specialize hh (d.f g₁.s),
      --     cases hh with ma hh,
      --     apply h₁,
      --     use ma.m,
      --     convert ma.h,
      --     change apply_devil_move _ _ = _,
      --     congr,
      --     apply play_at_players_eq.2,
      --   },
      -- },
      -- convert h₂; rw ←h₁,
    },
    sorry,
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