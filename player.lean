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

def apply_devil_move' (s : State) : Devil_move → Board
| (option.none) := s.board
| (option.some p) := {s.board with squares := s.board.squares \ {p}}

def apply_devil_move (s : State) (m : Devil_move) : State :=
apply_move s (apply_devil_move' s m)

-----

structure Angel (pw : ℕ) : Type :=
(f : Π (s : State),
  angel_has_valid_move pw s.board → Valid_angel_move pw s.board)

structure Devil : Type :=
(f : Π (s : State), Valid_devil_move s.board)

instance {pw : ℕ} : inhabited (Angel pw) :=
⟨⟨λ s h, ⟨h.some, h.some_spec⟩⟩⟩

instance : inhabited Devil :=
⟨⟨λ s, ⟨none, trivial⟩⟩⟩

def Angel.sup {pw pw₁ : ℕ} (a₁ : Angel pw₁) (a : Angel pw) : Prop :=
∀ s h, ∃ h₁, (a₁.f s h₁).m = (a.f s h).m

def Angel.sub {pw₁ pw : ℕ} (a : Angel pw₁) (a₁ : Angel pw) : Prop :=
a₁.sup a

def Valid_move_T := Board → Type

def Prev_moves (T : Valid_move_T) (s : State) :=
Π (s₁ : State), s₁.history.length < s.history.length → T s₁.board

def Angel.set_prev_moves {pw : ℕ} {s : State} (a : Angel pw)
  (pm : Prev_moves (Valid_angel_move pw) s) : Angel pw :=
begin
  refine ⟨λ s₁ h, _⟩,
  apply dite (s₁.history.length < s.history.length); intro h₁,
  { exact pm s₁ h₁ },
  { exact a.f s₁ h },
end

def Devil.set_prev_moves {s : State} (d : Devil)
  (pm : Prev_moves Valid_devil_move s) : Devil :=
begin
  refine ⟨λ s₁, _⟩,
  apply dite (s₁.history.length < s.history.length); intro h₁,
  { exact pm s₁ h₁ },
  { exact d.f s₁ },
end

-----

lemma angel_move_valid_ge_of {pw pw₁ : ℕ} {b : Board} {p : Angel_move}
  (h₁ : pw ≤ pw₁) (h₂ : angel_move_valid pw b p) :
  angel_move_valid pw₁ b p :=
⟨h₂.1, h₂.2.1.trans h₁, h₂.2.2⟩

lemma angel_has_valid_move_ge_of {pw pw₁ : ℕ} {b : Board}
  (h₁ : pw ≤ pw₁) (h₂ : angel_has_valid_move pw b) :
  angel_has_valid_move pw₁ b :=
by { cases h₂ with m h₂, use m, exact angel_move_valid_ge_of h₁ h₂ }