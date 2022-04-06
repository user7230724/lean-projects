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
(A : Point)

def board₀ : Board := ⟨set.univ, center⟩

-- Move

def A_move : Type := Point
def D_move : Type := option Point

def A_move_valid (pw : ℕ) (b : Board) (p : A_move) : Prop :=
p ≠ b.A ∧ dist p b.A ≤ pw ∧ p ∈ b.squares

def D_move_valid (b : Board) : D_move → Prop
| (option.none) := true
| (option.some p) := p ≠ b.A ∧ p ∈ b.squares

structure Valid_A_move (pw : ℕ) (b : Board) :=
(m : A_move)
(h : A_move_valid pw b m)

structure Valid_D_move (b : Board) :=
(m : D_move)
(h : D_move_valid b m)

def A_has_valid_move (pw : ℕ) (b : Board) :=
∃ (m : A_move), A_move_valid pw b m

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

structure A (pw : ℕ) : Type :=
(f : Π (s : State), s.act →
  A_has_valid_move pw s.board → Valid_A_move pw s.board)

structure D : Type :=
(f : Π (s : State), s.act → Valid_D_move s.board)

def apply_move (s : State) (b : Board) : State :=
{s with board := b, history := s.history ++ [s.board] }

def apply_A_move (s : State) (p : A_move) : State :=
apply_move s {s.board with A := p}

def apply_D_move' (s : State) : D_move → Board
| (option.none) := s.board
| (option.some p) := {s.board with squares := s.board.squares \ {p}}

def apply_D_move (s : State) (m : D_move) : State :=
apply_move s (apply_D_move' s m)

-- Game

@[ext] structure Game (pw : ℕ) : Type :=
(a : A pw)
(d : D)
(s : State)

def init_game {pw : ℕ} (a : A pw) (d : D) (s : State) : Game pw :=
{ a := a, d := d, s := s }

def Game.act {pw : ℕ} (g : Game pw) : Prop :=
g.s.act

def Game.set_state {pw : ℕ} (g : Game pw) (s₁ : State) : Game pw :=
{g with s := s₁}

def play_A_move_at' {pw pw₁ : ℕ} (a₁ : A pw₁) (g : Game pw) (hs h) :=
g.set_state (apply_A_move g.s (a₁.f g.s hs h).m)

def Game.finish {pw : ℕ} (g : Game pw) : Game pw :=
g.set_state g.s.finish

def play_A_move_at {pw : ℕ} (g : Game pw) :=
if h : g.act ∧ A_has_valid_move pw g.s.board
then play_A_move_at' g.a g h.1 h.2
else g.finish

def play_D_move_at {pw : ℕ} (g : Game pw) (hs) :=
g.set_state (apply_D_move g.s (g.d.f g.s hs).m)

def Game.play_move {pw : ℕ} (g : Game pw) :=
if hs : g.act
then play_A_move_at (play_D_move_at g hs)
else g

def Game.play {pw : ℕ} (g : Game pw) (n : ℕ) :=
(Game.play_move^[n]) g

def Game.A_wins {pw : ℕ} (g : Game pw) :=
∀ (n : ℕ), (g.play n).act

def A_hws_at (pw : ℕ) (s : State) :=
∃ (a : A pw), ∀ (d : D), (init_game a d s).A_wins

def A_hws (pw : ℕ) := A_hws_at pw state₀