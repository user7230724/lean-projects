import tactic.induction
import data.int.basic
import data.set.basic

import .point .dist .board .state .move .strategy

noncomputable theory
open_locale classical

@[ext] structure Game (pw : ℕ) : Type :=
(a : Angel_st pw)
(d : Devil_st)
(s : State)
(done : Prop)

def init_game {pw : ℕ} (a : Angel_st pw) (d : Devil_st) : Game pw :=
{ a := a,
  d := d,
  s := state₀,
  done := false }

def play_angel_move_at {pw : ℕ} (g : Game pw) :=
if h : angel_has_valid_move pw g.s.board
then {g with s := apply_angel_move g.s (g.a g.s h).m }
else {g with done := true}

def play_devil_move_at {pw : ℕ} (g : Game pw) :=
{g with s := apply_devil_move g.s (g.d g.s).m}

def play_move_at {pw : ℕ} (g : Game pw) :=
if g.done then g else
play_angel_move_at (play_devil_move_at g)

def play_at {pw : ℕ} (g : Game pw) (n : ℕ) :=
(play_move_at^[n]) g

def angel_wins_at {pw : ℕ} (g : Game pw) :=
∀ (n : ℕ), ¬(play_at g n).done

def devil_wins_at {pw : ℕ} (g : Game pw) :=
∃ (n : ℕ), (play_at g n).done

-----

lemma done_play_at_succ_of {pw : ℕ} {g : Game pw} {n : ℕ}
  (h : (play_at g n).done) : (play_at g n.succ).done :=
begin
  sorry
end

lemma done_play_at_ge_of {pw : ℕ} {g : Game pw} {n m : ℕ}
  (h₁ : n ≤ m) (h₂ : (play_at g n).done) : (play_at g m).done :=
begin
  sorry
end