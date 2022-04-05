import tactic.induction
import data.int.basic
import data.set.basic

import .board

noncomputable theory
open_locale classical

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

instance : inhabited State := ⟨state₀⟩

def State.finish (s : State) : State :=
{s with act := false}

@[reducible]
def State.len (s : State) : ℕ :=
s.history.length

def State.nth (s : State) (n : ℕ) : option Board :=
(s.history ++ [s.board]).nth n

-----

lemma hist_ne_of_hist_len_ne {s₁ s₂ : State}
  (h : s₁.history.length ≠ s₂.history.length) :
  s₁.history ≠ s₂.history :=
by { contrapose! h, rw h }

lemma hist_len_finish {s : State} :
  s.finish.history.length = s.history.length := rfl

-- lemma 