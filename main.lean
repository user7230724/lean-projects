import tactic.induction
import data.int.basic
import data.set.basic
import logic.function.iterate

import .point .dist .board .state .move .game

noncomputable theory
open_locale classical

-- Keep definitions intuitive!
-- Do not generalize too much!

def angel_wins {pw : ℕ} (a : Angel_st pw) (d : Devil_st) :=
angel_wins_at (init_game a d)

def devil_wins {pw : ℕ} (a : Angel_st pw) (d : Devil_st) :=
devil_wins_at (init_game a d)

def angel_hws (pw : ℕ) :=
∃ (a : Angel_st pw), ∀ (d : Devil_st), angel_wins a d

def devil_hws (pw : ℕ) :=
∃ (d : Devil_st), ∀ (a : Angel_st pw), devil_wins a d

-----

lemma angel_pw_0_has_not_win_st : ¬angel_hws 0 :=
begin
  sorry
  -- rintro ⟨st, h⟩, apply h default, clear h, use 1,
  -- change Game.done (ite _ _ _), split_ifs, { exact h }, clear h,
  -- change Game.done (dite _ _ _), split_ifs, swap, { trivial },
  -- rcases h with ⟨p, h₁, h₂, h₃⟩,
  -- rw [nat.le_zero_iff, dist_eq_zero_iff] at h₂, contradiction,
end

lemma angel_pw_1_has_not_win_st : ¬angel_hws 1 :=
begin
  sorry
end

lemma angel_pw_2_hws : angel_hws 2 :=
begin
  sorry
end

lemma angel_pw_ge_hws_of {pw pw₁ : ℕ}
  (h₁ : pw ≤ pw₁) (h₂ : angel_hws pw) : angel_hws pw₁ :=
begin
  refine ⟨λ s h, _, _⟩,
  { have h₃ := angel_has_valid_move_le_of h₁ h, use (h₂.some s h₃).m,
    apply angel_move_valid_ge_of h₁, exact (h₂.some s h₃).h },
  {
    rintro d n,
    let a := h₂.some,
    have h₃ := h₂.some_spec d n,
    induction' n, exact h₃,
    specialize ih h₁ d (mt done_play_at_succ_of h₃),

    unfold play_at,
    rw function.iterate_succ_apply',

    let g := _,
    change ¬Game.done g at ih,
    change ¬Game.done (play_move_at g),
    change ¬Game.done (ite _ _ _),
    split_ifs,

    change ¬Game.done (dite _ _ _),
    split_ifs,
    sorry,
    sorry,
  },
end

#exit

-----

theorem angel_hws_iff_pw_ge_2 {pw : ℕ} :
  angel_hws pw ↔ 2 ≤ pw :=
begin
  cases pw, simp [angel_pw_0_has_not_win_st],
  cases pw, simp [angel_pw_1_has_not_win_st], simp [nat.succ_le_succ],
  refine angel_pw_ge_hws_of _ angel_pw_2_hws, simp [nat.succ_le_succ],
end

-- example {a : ℤ}
--   (h : 0 < a) :
--   int.to_nat 0 < a.to_nat :=
-- begin
--   library_search,
-- end