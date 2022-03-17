import tactic.induction
import data.int.basic
import data.set.basic

import .point .dist .board .state

noncomputable theory
open_locale classical

def Angel_move : Type := Point
def Devil_move : Type := option Point

def angel_move_valid (pw : ℕ) (b : Board) (p : Angel_move) : Prop :=
p ≠ b.angel ∧ dist p b.angel ≤ pw ∧ p ∈ b.squares

def devil_move_valid (b : Board) : Devil_move → Prop
| (option.none) := true
| (option.some p) := p ≠ b.angel ∧ p ∈ b.squares

def angel_has_valid_move (pw : ℕ) (b : Board) :=
∃ (m : Angel_move), angel_move_valid pw b m

structure Valid_angel_move (pw : ℕ) (b : Board) :=
(m : Angel_move)
(h : angel_move_valid pw b m)

structure Valid_devil_move (b : Board) :=
(m : Devil_move)
(h : devil_move_valid b m)

def apply_move (s : State) (b : Board) : State :=
{ board := b, history := s.board :: s.history }

def apply_angel_move (s : State) (p : Angel_move) : State :=
apply_move s {s.board with angel := p}

def apply_devil_move (s : State) : Devil_move → State
| (option.none) := apply_move s s.board
| (option.some p) := apply_move s
  {s.board with squares := s.board.squares \ {p}}

-----

lemma angel_move_valid_ge_of {pw pw₁ : ℕ} {b : Board} {p : Angel_move}
  (h₁ : pw ≤ pw₁) (h₂ : angel_move_valid pw b p) :
  angel_move_valid pw₁ b p :=
begin
  sorry
end

lemma angel_has_valid_move_le_of {pw pw₁ : ℕ} {b : Board}
  (h₁ : pw ≤ pw₁) (h₂ : angel_has_valid_move pw₁ b) :
  angel_has_valid_move pw b :=
begin
  sorry
end