import tactic.induction
import data.int.basic
import data.set.basic

noncomputable theory
open_locale classical

-- Keep definitions intuitive!
-- Do not generalize too much!

@[ext] structure Point : Type :=
(x y : ℤ)

def center : Point := ⟨0, 0⟩
instance : inhabited Point := ⟨center⟩

def dist (p₁ p₂ : Point) : ℕ :=
(max (|p₁.x - p₂.x|) (|p₁.y - p₂.y|)).to_nat

structure Board : Type :=
(squares : set Point)
(angel : Point)

def board₀ : Board := ⟨set.univ, center⟩
instance : inhabited Board := ⟨board₀⟩

structure State : Type :=
(board : Board)
(history : list Board)

def state₀ : State := ⟨board₀, []⟩
instance : inhabited State := ⟨state₀⟩

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

def Angel_st (pw : ℕ) : Type :=
Π (s : State), angel_has_valid_move pw s.board → Valid_angel_move pw s.board

def Devil_st : Type :=
Π (s : State), Valid_devil_move s.board

structure Game (pw : ℕ) : Type :=
(a : Angel_st pw)
(d : Devil_st)
(s : State)
(done : Prop)

def init_game {pw : ℕ} (a : Angel_st pw) (d : Devil_st) : Game pw :=
{ a := a,
  d := d,
  s := state₀,
  done := false }

def apply_move (s : State) (b : Board) : State :=
{ board := b, history := s.board :: s.history }

def apply_angel_move (s : State) (p : Angel_move) : State :=
apply_move s {s.board with angel := p}

def apply_devil_move (s : State) : Devil_move → State
| (option.none) := apply_move s s.board
| (option.some p) := apply_move s
  {s.board with squares := s.board.squares \ {p}}

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
¬∃ (n : ℕ), (play_at g n).done

def devil_wins_at {pw : ℕ} (g : Game pw) :=
¬angel_wins_at g

def angel_wins {pw : ℕ} (a : Angel_st pw) (d : Devil_st) :=
angel_wins_at (init_game a d)

def devil_wins {pw : ℕ} (a : Angel_st pw) (d : Devil_st) :=
¬angel_wins a d

def angel_has_win_st (pw : ℕ) :=
∃ (a : Angel_st pw), ∀ (d : Devil_st), angel_wins a d

def devil_has_win_st (pw : ℕ) :=
∃ (d : Devil_st), ∀ (a : Angel_st pw), devil_wins a d

-----

theorem angel_has_win_st_iff_pw_ge_2 {pw : ℕ} :
  angel_has_win_st pw ↔ 2 ≤ pw :=
begin
  sorry
end

-- example {a b c : ℕ}
--   (h₁ : a < b)
--   (h₂ : b ≤ c) :
--   a < c :=
-- begin
--   library_search,
-- end