import tactic
import tactic.induction

noncomputable theory
open_locale classical

-- Point

@[ext] structure Point : Type :=
(x y : ℤ)

def center : Point := ⟨0, 0⟩

def dist (p₁ p₂ : Point) : ℕ :=
(max (|p₁.x - p₂.x|) (|p₁.y - p₂.y|)).to_nat

-- Board

structure Board : Type :=
(squares : set Point)
(angel : Point)

def board₀ : Board := ⟨set.univ, center⟩

-- Move

def Angel_move : Type := Point
def Devil_move : Type := option Point

def angel_move_valid (pw : ℕ) (b : Board) (p : Angel_move) : Prop :=
p ≠ b.angel ∧ dist p b.angel ≤ pw ∧ p ∈ b.squares

def devil_move_valid (b : Board) : Devil_move → Prop
| (option.none) := true
| (option.some p) := p ≠ b.angel ∧ p ∈ b.squares

structure Valid_angel_move (pw : ℕ) (b : Board) :=
(m : Angel_move)
(h : angel_move_valid pw b m)

structure Valid_devil_move (b : Board) :=
(m : Devil_move)
(h : devil_move_valid b m)

def angel_has_valid_move (pw : ℕ) (b : Board) :=
∃ (m : Angel_move), angel_move_valid pw b m

-- State

structure State : Type :=
(board : Board)
(history : list Board)
(act : Prop)

def init_state (b : Board) : State :=
{ board := b,
  history := [],
  act := true }

def state₀ : State :=
init_state board₀

def State.finish (s : State) : State :=
{s with act := false}

-- Player

structure Angel (pw : ℕ) : Type :=
(f : Π (s : State), s.act →
  angel_has_valid_move pw s.board → Valid_angel_move pw s.board)

structure Devil : Type :=
(f : Π (s : State), s.act → Valid_devil_move s.board)

-- Game

@[ext] structure Game (pw : ℕ) : Type :=
(a : Angel pw)
(d : Devil)
(s : State)

def init_game {pw : ℕ} (a : Angel pw) (d : Devil) (s : State) : Game pw :=
{ a := a, d := d, s := s }

def Game.act {pw : ℕ} (g : Game pw) : Prop :=
g.s.act

def apply_move (s : State) (b : Board) : State :=
{s with board := b, history := s.history ++ [s.board] }

def apply_angel_move (s : State) (p : Angel_move) : State :=
apply_move s {s.board with angel := p}

def apply_devil_move' (s : State) : Devil_move → Board
| (option.none) := s.board
| (option.some p) := {s.board with squares := s.board.squares \ {p}}

def apply_devil_move (s : State) (m : Devil_move) : State :=
apply_move s (apply_devil_move' s m)

def Game.set_state {pw : ℕ} (g : Game pw) (s₁ : State) : Game pw :=
{g with s := s₁}

def play_angel_move_at' {pw pw₁ : ℕ} (a₁ : Angel pw₁) (g : Game pw) (hs h) :=
g.set_state (apply_angel_move g.s (a₁.f g.s hs h).m)

def Game.finish {pw : ℕ} (g : Game pw) : Game pw :=
g.set_state g.s.finish

def play_angel_move_at {pw : ℕ} (g : Game pw) :=
if h : g.act ∧ angel_has_valid_move pw g.s.board
then play_angel_move_at' g.a g h.1 h.2
else g.finish

def play_devil_move_at {pw : ℕ} (g : Game pw) (hs) :=
g.set_state (apply_devil_move g.s (g.d.f g.s hs).m)

def Game.play_move {pw : ℕ} (g : Game pw) :=
if hs : g.act
then play_angel_move_at (play_devil_move_at g hs)
else g

def Game.play {pw : ℕ} (g : Game pw) (n : ℕ) :=
(Game.play_move^[n]) g

def Game.angel_wins {pw : ℕ} (g : Game pw) :=
∀ (n : ℕ), (g.play n).act

def angel_hws_at (pw : ℕ) (s : State) :=
∃ (a : Angel pw), ∀ (d : Devil), (init_game a d s).angel_wins

def angel_hws (pw : ℕ) := angel_hws_at pw state₀