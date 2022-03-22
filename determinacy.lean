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

lemma not_devil_hws_at_play_of_not_devil_hws {pw n : ℕ} {g : Game pw}
  (h : ¬devil_hws_at pw g.s) :
  ¬devil_hws_at pw (g.play n).s :=
begin
  sorry
end

-- #exit

lemma angel_hws_at_of {pw : ℕ} {s : State}
  (h : ¬devil_hws_at pw s) : angel_hws_at pw s :=
begin
  let A := mk_angel_st_for_not_devil_hws pw,
  use A,
  rintro d n,
  induction n with n ih, { triv },
  rw play_at_succ',
  let g : Game pw := _,
  change g.act at ih,
  change g.play_move.act,
  let s := g.s,
  let md := d.f s,
  let s' := apply_devil_move s md.m,
  rw play_move_at_act ih,

  have h₁ : play_devil_move_at g = g.set_state s',
  {
    convert play_devil_move_eq,
    change apply_devil_move _ (d.f s).m = _,
    congr,
    symmetry,
    exact play_at_players_eq.2,
  },
  rw h₁, clear h₁,

  have h₁ : angel_has_valid_move pw s'.board,
  {
    have h₁ : ¬devil_hws_at pw s,
    {
      exact not_devil_hws_at_play_of_not_devil_hws h,
    },
    obtain ⟨ma, -⟩ := exi_angel_move_of_not_devil_hws h₁ md,
    exact ⟨_, ma.h⟩,
  },

  change Game.act (dite _ _ _),
  change (g.set_state s').s with s',
  rw dif_pos h₁,
  exact ih,
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